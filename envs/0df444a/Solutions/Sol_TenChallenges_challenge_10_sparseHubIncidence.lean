-- Prove2me | solution 1 for TenChallenges.challenge_10_sparseHubIncidence
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:17:59.647964+00:00
-- url     : https://prove2.me/submissions/0a460729-52d3-49eb-af7c-24387af21147

import Definitions.Def_TenChallenges_Challenge_10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Equiv.Finset
import Mathlib.Logic.Function.DependsOn
import Mathlib.Order.TeichmullerTukey
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete

universe u v

/- Inlined from Continuation/UnfriendlyEnergy.lean. -/
/-!
# Directed cut energy for finite color flips

The energy counts both orientations of each edge. Its sign agrees with ordinary
cut improvement, while a singleton perturbation has the uniform bound `4 * k`.
All identities involving sums assume that the flipped vertices have finite degree.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators symmDiff

variable {V : Type u}

open Classical in
/-- Reverse the colors on a finite vertex set. -/
noncomputable def flip (c : V → Bool) (S : Finset V) : V → Bool :=
  fun x => if x ∈ S then !(c x) else c x

/-- The indicator that a directed pair crosses the color classes. -/
def cutIndicator (c : V → Bool) (e : V × V) : ℤ :=
  if c e.1 ≠ c e.2 then 1 else 0

open Classical in
/-- Change in the directed cut indicator along one adjacent pair. -/
noncomputable def edgeDelta (G : SimpleGraph V) (c d : V → Bool) (e : V × V) : ℤ :=
  if G.Adj e.1 e.2 then cutIndicator d e - cutIndicator c e else 0

/-- Directed cut gain from a finite color flip; finite-degree hypotheses ensure finite support. -/
noncomputable def gain (G : SimpleGraph V) (c : V → Bool) (S : Finset V) : ℤ :=
  ∑ᶠ e, edgeDelta G c (flip c S) e

/-- Directed edges that become crossing edges after the flip. -/
def gained (G : SimpleGraph V) (c : V → Bool) (S : Finset V) : Set (V × V) :=
  {e | edgeDelta G c (flip c S) e = 1}

/-- Directed edges that cease to be crossing edges after the flip. -/
def lost (G : SimpleGraph V) (c : V → Bool) (S : Finset V) : Set (V × V) :=
  {e | edgeDelta G c (flip c S) e = -1}

/-- No finite flip of finite-degree vertices in `A` improves the cut. -/
def StrongMaximal (G : SimpleGraph V) (A : Set V) (c : V → Bool) : Prop :=
  ∀ S : Finset V, (S : Set V) ⊆ A →
    (∀ x ∈ S, (G.neighborSet x).Finite) → gain G c S ≤ 0

/-- Adjacent directed pairs with at least one endpoint in `S`. -/
def incident (G : SimpleGraph V) (S : Finset V) : Set (V × V) :=
  {e | G.Adj e.1 e.2 ∧ (e.1 ∈ S ∨ e.2 ∈ S)}

@[simp] theorem flip_empty (c : V → Bool) : flip c ∅ = c :=
  funext fun x => if_neg (Finset.notMem_empty x)

@[simp] theorem gain_empty (G : SimpleGraph V) (c : V → Bool) : gain G c ∅ = 0 := by
  simp [gain, edgeDelta]

open Classical in
/-- Two finite flips compose by symmetric difference. -/
theorem flip_symmDiff (c : V → Bool) (S T : Finset V) :
    flip c (S ∆ T) = flip (flip c S) T := by
  funext x
  by_cases hxS : x ∈ S
  all_goals by_cases hxT : x ∈ T
  all_goals simp_all [flip, Finset.mem_symmDiff]

/-- Finite sets of finite-degree vertices meet only finitely many directed edges. -/
theorem incident_finite (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) : (incident G S).Finite := by
  exact (S.finite_toSet.biUnion (fun x hx =>
    ((hS x hx).image (fun y => (x, y))).union
      ((hS x hx).image (fun y => (y, x))))).subset
    (fun e he => he.2.elim
      (fun hx => Set.mem_iUnion.mpr ⟨e.1, Set.mem_iUnion.mpr
        ⟨hx, Or.inl ⟨e.2, he.1, rfl⟩⟩⟩)
      (fun hy => Set.mem_iUnion.mpr ⟨e.2, Set.mem_iUnion.mpr
        ⟨hy, Or.inr ⟨e.1, he.1.symm, rfl⟩⟩⟩))

private theorem edgeDelta_flip_zero (G : SimpleGraph V) (c : V → Bool)
    (S : Finset V) (e : V × V) (h : e ∉ incident G S) :
    edgeDelta G c (flip c S) e = 0 := by
  classical
  by_cases ha : G.Adj e.1 e.2
  · simp [edgeDelta, cutIndicator, flip, ha,
      (show e.1 ∉ S from fun hx => h ⟨ha, Or.inl hx⟩),
      (show e.2 ∉ S from fun hy => h ⟨ha, Or.inr hy⟩)]
  · simp [edgeDelta, ha]

/-- A finite flip changes only incident directed edges. -/
theorem support_edgeDelta_flip_subset (G : SimpleGraph V) (c : V → Bool) (S : Finset V) :
    Function.support (edgeDelta G c (flip c S)) ⊆ incident G S :=
  fun e he => Classical.byContradiction
    (fun hn => he (edgeDelta_flip_zero G c S e hn))

/-- The directed gain function has finite support for a flip of finite-degree vertices. -/
theorem gain_hasFiniteSupport (G : SimpleGraph V) (c : V → Bool) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) :
    (edgeDelta G c (flip c S)).HasFiniteSupport :=
  (incident_finite G S hS).subset (support_edgeDelta_flip_subset G c S)

/-- A flip of finite-degree vertices gains only finitely many directed edges. -/
theorem gained_finite (G : SimpleGraph V) (c : V → Bool) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) : (gained G c S).Finite :=
  (gain_hasFiniteSupport G c S hS).subset
    (fun _ he => ne_of_eq_of_ne he (by decide : (1 : ℤ) ≠ 0))

/-- A flip of finite-degree vertices loses only finitely many directed edges. -/
theorem lost_finite (G : SimpleGraph V) (c : V → Bool) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) : (lost G c S).Finite :=
  (gain_hasFiniteSupport G c S hS).subset
    (fun _ he => ne_of_eq_of_ne he (by decide : (-1 : ℤ) ≠ 0))

private theorem edgeDelta_add (G : SimpleGraph V) (c d q : V → Bool) (e : V × V) :
    edgeDelta G c q e = edgeDelta G c d e + edgeDelta G d q e := by
  unfold edgeDelta
  split_ifs
  all_goals omega

open Classical in
/-- Cut gains add along successive finite flips. -/
theorem gain_symmDiff (G : SimpleGraph V) (c : V → Bool) (S T : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite)
    (hT : ∀ x ∈ T, (G.neighborSet x).Finite) :
    gain G c (S ∆ T) = gain G c S + gain G (flip c S) T := by
  unfold gain
  rw [flip_symmDiff]
  rw [show edgeDelta G c (flip (flip c S) T) =
      (fun e => edgeDelta G c (flip c S) e +
        edgeDelta G (flip c S) (flip (flip c S) T) e) from
    funext (edgeDelta_add G c (flip c S) (flip (flip c S) T))]
  exact finsum_add_distrib (gain_hasFiniteSupport G c S hS)
    (gain_hasFiniteSupport G (flip c S) T hT)

/-- Gain depends only on colors at endpoints of incident edges. -/
theorem gain_congr_of_incident_eq (G : SimpleGraph V) (c d : V → Bool) (S : Finset V)
    (h : ∀ e ∈ incident G S, c e.1 = d e.1 ∧ c e.2 = d e.2) :
    gain G c S = gain G d S := by
  classical
  apply finsum_congr
  intro e
  by_cases he : e ∈ incident G S
  · simp only [edgeDelta, cutIndicator, flip, (h e he).1, (h e he).2]
    rfl
  · exact (edgeDelta_flip_zero G c S e he).trans (edgeDelta_flip_zero G d S e he).symm

/-- Every admissible finite-flip energy depends on finitely many color coordinates. -/
theorem gain_finite_dependence (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) :
    ∃ W : Finset V, ∀ c d : V → Bool,
      (∀ x ∈ W, c x = d x) → gain G c S = gain G d S := by
  classical
  let E := (incident_finite G S hS).toFinset
  exact ⟨E.image Prod.fst ∪ E.image Prod.snd, fun c d h =>
    gain_congr_of_incident_eq G c d S (fun e he =>
      let hE : e ∈ E := (incident_finite G S hS).mem_toFinset.mpr he
      ⟨h e.1 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, hE, rfl⟩)),
        h e.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, hE, rfl⟩))⟩)⟩

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyStrongMaximal.lean. -/
/-!
# Strong maximality on finite-degree vertices with a fixed boundary

Finite flip inequalities depend on finitely many color coordinates. Their
finite satisfiability therefore gives a global coloring by compactness.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.StrongMaximalCompactness

open scoped symmDiff

variable {V : Type u}

private theorem isClosed_of_finite_dependence [TopologicalSpace Bool] [DiscreteTopology Bool]
    (P : (V → Bool) → Prop) (W : Finset V)
    (hP : ∀ c d, Set.EqOn c d (W : Set V) → (P c ↔ P d)) :
    IsClosed {c | P c} := by
  classical
  let res : (V → Bool) → (W → Bool) := fun c x => c x.1
  let ext : (W → Bool) → (V → Bool) := fun c x => if hx : x ∈ W then c ⟨x, hx⟩ else false
  have hres : Continuous res := continuous_pi fun x => continuous_apply x.1
  have heq : {c | P c} = res ⁻¹' {d | P (ext d)} :=
    Set.ext fun c => hP c (ext (res c))
      (fun x hx => by simp only [ext, res, dif_pos (show x ∈ W from hx)])
  rw [heq]
  exact (isClosed_discrete _).preimage hres

private theorem exists_boolean_coloring {ι : Type v} (D : Set V) (p : V → Bool)
    (P : ι → (V → Bool) → Prop)
    (hlocal : ∀ i, ∃ W : Finset V,
      ∀ c d, Set.EqOn c d (W : Set V) → (P i c ↔ P i d))
    (hfinite : ∀ F : Finset ι, ∃ c, Set.EqOn c p D ∧ ∀ i ∈ F, P i c) :
    ∃ c, Set.EqOn c p D ∧ ∀ i, P i c := by
  classical
  let : TopologicalSpace Bool := ⊥
  let : DiscreteTopology Bool := ⟨rfl⟩
  let : CompactSpace (V → Bool) := inferInstance
  let B : Set (V → Bool) := {c | Set.EqOn c p D}
  have hB : IsClosed B := by
    simpa only [B, Set.EqOn, Set.ofPred_forall] using
      (isClosed_biInter fun x (_ : x ∈ D) =>
        isClosed_eq (continuous_apply x) (continuous_const (y := p x)))
  have hPc : ∀ i, IsClosed {c | P i c} := fun i =>
    let ⟨W, hW⟩ := hlocal i
    isClosed_of_finite_dependence (P i) W hW
  have hF : ∀ F : Finset ι, (B ∩ ⋂ i ∈ F, {c | P i c}).Nonempty := fun F => by
    simpa only [B, Set.Nonempty, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      using hfinite F
  obtain ⟨c, hc⟩ := hB.isCompact.inter_iInter_nonempty (fun i => {c | P i c}) hPc hF
  exact ⟨c, hc.1, fun i => Set.mem_iInter.mp hc.2 i⟩

private theorem exists_maximal_flip_subset [DecidableEq V] {C : Type v}
    (flip : C → Finset V → C) (gain : C → Finset V → ℤ) (p : C) (U : Finset V)
    (hcocycle : ∀ c S T, S ⊆ U → T ⊆ U →
      gain c (S ∆ T) = gain c S + gain (flip c S) T) :
    ∃ T, T ⊆ U ∧ ∀ S, S ⊆ U → gain (flip p T) S ≤ 0 := by
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image U.powerset (gain p) U.powerset_nonempty
  refine ⟨T, Finset.mem_powerset.mp hT, ?_⟩
  intro S hS
  have hTS : T ∆ S ⊆ U := Finset.symmDiff_subset_union.trans
    (Finset.union_subset (Finset.mem_powerset.mp hT) hS)
  have hle := hmax (T ∆ S) (Finset.mem_powerset.mpr hTS)
  rw [hcocycle p T S (Finset.mem_powerset.mp hT) hS] at hle
  exact (add_le_iff_nonpos_right _).mp hle

/-- Every prescribed boundary coloring extends to a coloring admitting no improving
finite flip of finite-degree vertices outside the boundary. -/
theorem exists_strongMaximal_eqOn (G : SimpleGraph V) (D : Set V) (p : V → Bool) :
    ∃ c, Set.EqOn c p D ∧ Energy.StrongMaximal G Dᶜ c := by
  classical
  let ι : Type u := {S : Finset V // (S : Set V) ⊆ Dᶜ ∧
    ∀ x ∈ S, (G.neighborSet x).Finite}
  let P : ι → (V → Bool) → Prop := fun S c => Energy.gain G c S.1 ≤ 0
  have hlocal : ∀ i, ∃ W : Finset V,
      ∀ c d, Set.EqOn c d (W : Set V) → (P i c ↔ P i d) := by
    intro i
    obtain ⟨W, hW⟩ := Energy.gain_finite_dependence G i.1 i.2.2
    exact ⟨W, fun c d hcd => Iff.of_eq
      (congrArg (fun z : ℤ => z ≤ 0) (hW c d (fun x hx => hcd hx)))⟩
  have hfinite : ∀ F : Finset ι, ∃ c, Set.EqOn c p D ∧ ∀ i ∈ F, P i c := by
    intro F
    let U : Finset V := F.biUnion fun i => i.1
    have hU : ∀ x ∈ U, (G.neighborSet x).Finite := fun x hx =>
      let ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
      i.2.2 x hxi
    have hUD : (U : Set V) ⊆ Dᶜ := fun x hx =>
      let ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
      i.2.1 hxi
    obtain ⟨T, hTU, hstable⟩ := exists_maximal_flip_subset Energy.flip (Energy.gain G) p U
      (fun c S T hSU hTU => Energy.gain_symmDiff G c S T
        (fun x hx => hU x (hSU hx)) (fun x hx => hU x (hTU hx)))
    refine ⟨Energy.flip p T, ?_, fun i hi =>
      hstable i.1 (fun x hx => Finset.mem_biUnion.mpr ⟨i, hi, hx⟩)⟩
    exact fun x hx => if_neg (fun hxt => hUD (hTU hxt) hx)
  obtain ⟨c, hcD, hc⟩ := exists_boolean_coloring D p P hlocal hfinite
  exact ⟨c, hcD, fun S hS hfin => hc ⟨S, hS, hfin⟩⟩

end TenChallenges.Continuation.StrongMaximalCompactness

/- Inlined from Continuation/UnfriendlyMaximalWitnesses.lean. -/
/-!
# Inclusion-maximal closed witnesses

In a compact space of colourings, a given collection of satisfied closed
conditions can be extended to an inclusion-maximal one.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.MaximalWitnesses

theorem exists_maximal_witnesses {X : Type u} {I : Type v} [TopologicalSpace X]
    {K : Set X} (hk : IsCompact K) (W : X → Set I)
    (hclosed : ∀ i, IsClosed {x | i ∈ W x}) {a : X} (ha : a ∈ K) :
    ∃ c ∈ K, W a ⊆ W c ∧ ∀ d ∈ K, W c ⊆ W d → W d ⊆ W c := by
  classical
  let A : Set (Set I) := {s | ∃ c ∈ K, s ⊆ W c}
  have hchar : Order.IsOfFiniteCharacter A := by
    intro s
    constructor
    · exact fun ⟨c, hc, h⟩ t ht _ => ⟨c, hc, ht.trans h⟩
    · intro h
      obtain ⟨c, hc, hs⟩ := hk.inter_iInter_nonempty
        (fun i : s => {x | i.val ∈ W x}) (fun i => hclosed i.val) (fun F => by
          obtain ⟨c, hc, ht⟩ := h (Subtype.val '' (F : Set s))
            (fun _ ⟨i, _, he⟩ => he ▸ i.property) (F.finite_toSet.image _)
          exact ⟨c, hc, Set.mem_iInter₂.mpr fun i hi => ht ⟨i, hi, rfl⟩⟩)
      exact ⟨c, hc, fun i hi => Set.mem_iInter.mp hs ⟨i, hi⟩⟩
  obtain ⟨m, ham, hm⟩ := hchar.exists_maximal (x := W a) ⟨a, ha, Set.Subset.rfl⟩
  obtain ⟨c, hc, hmc⟩ := hm.prop
  refine ⟨c, hc, ham.trans hmc, ?_⟩
  intro d hd hcd
  exact (hm.le_of_ge (show W d ∈ A from ⟨d, hd, Set.Subset.rfl⟩) (hmc.trans hcd)).trans hmc

end TenChallenges.Continuation.MaximalWitnesses

/- Inlined from Continuation/UnfriendlyStrongTopology.lean. -/
/-! # Closedness of strong maximality under finite flips -/

set_option autoImplicit false

namespace TenChallenges.Continuation.StrongTopology

variable {V : Type*}

/-- Strongly maximal colourings form a closed subset of the product of discrete bits. -/
theorem isClosed_strongMaximal (G : SimpleGraph V) (A : Set V)
    [TopologicalSpace Bool] [DiscreteTopology Bool] :
    IsClosed {c | Energy.StrongMaximal G A c} := by
  simp only [Energy.StrongMaximal, Set.ofPred_forall]
  refine isClosed_iInter fun S => isClosed_iInter fun _ => isClosed_iInter fun hfin => ?_
  obtain ⟨W, hW⟩ := Energy.gain_finite_dependence G S hfin
  have hdep : DependsOn (fun c => Energy.gain G c S) (W : Set V) := fun {c d} => hW c d
  obtain ⟨g, hg⟩ := dependsOn_iff_exists_comp.mp hdep
  change IsClosed ((fun c => Energy.gain G c S) ⁻¹' Set.Iic 0)
  rw [hg, Set.preimage_comp]
  exact (isClosed_discrete _).preimage (Pi.continuous_domRestrict _)

end TenChallenges.Continuation.StrongTopology

/- Inlined from Continuation/UnfriendlyEnergyUF.lean. -/
/-!
# Strong maximality implies unfriendliness at finite-degree vertices

A singleton flip changes the directed cut by twice the excess of same-colored
neighbors. Thus a strongly maximal coloring is unfriendly wherever the vertex
has finite degree and lies outside the prescribed boundary.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators Cardinal

variable {V : Type u}

private theorem neighColored_card_eq (G : SimpleGraph V) (c : V → Bool) (v : V)
    (hN : (G.neighborSet v).Finite) (b : Bool) :
    #(NeighColored G (fun x => some (c x)) v (some b)) =
      ((hN.toFinset.filter fun w => c w = b).card : Cardinal) := by
  classical
  have heq : G.neighborSet v ∩ (fun x => some (c x)) ⁻¹' {some b} =
      ((hN.toFinset.filter fun w => c w = b) : Set V) := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Option.some.injEq, Finset.mem_coe, Finset.mem_filter, hN.mem_toFinset]
  unfold NeighColored
  rw [heq, Cardinal.mk_fintype]
  simp

private theorem edgeDelta_swap (G : SimpleGraph V) (c d : V → Bool) (x y : V) :
    edgeDelta G c d (x, y) = edgeDelta G c d (y, x) := by
  simp only [edgeDelta, cutIndicator, ne_comm]
  rw [G.adj_comm x y]

private theorem bool_flip_indicator : ∀ a b : Bool,
    (if (!a) ≠ b then (1 : ℤ) else 0) - (if a ≠ b then 1 else 0) =
      (if b = a then 1 else -1) := by decide

/-- The directed cut gain of a singleton flip is twice the local color imbalance. -/
theorem gain_singleton (G : SimpleGraph V) (c : V → Bool) (v : V)
    (hN : (G.neighborSet v).Finite) :
    gain G c {v} = 2 *
      (((hN.toFinset.filter fun w => c w = c v).card : ℤ) -
        ((hN.toFinset.filter fun w => c w ≠ c v).card : ℤ)) := by
  classical
  let N : Finset V := hN.toFinset
  let R : Finset (V × V) := N.image fun w => (v, w)
  let C : Finset (V × V) := N.image fun w => (w, v)
  have hE : incident G {v} ⊆ ((R ∪ C : Finset (V × V)) : Set (V × V)) :=
    fun e he => he.2.elim
      (fun hx =>
        let hxv : e.1 = v := Finset.mem_singleton.mp hx
        Finset.mem_union_left C (Finset.mem_image.mpr
          ⟨e.2, hN.mem_toFinset.mpr (hxv ▸ he.1), Prod.ext hxv.symm rfl⟩))
      (fun hy =>
        let hyv : e.2 = v := Finset.mem_singleton.mp hy
        Finset.mem_union_right R (Finset.mem_image.mpr
          ⟨e.1, hN.mem_toFinset.mpr (hyv ▸ he.1.symm), Prod.ext rfl hyv.symm⟩))
  have hsum : gain G c {v} = ∑ e ∈ R ∪ C, edgeDelta G c (flip c {v}) e :=
    finsum_eq_sum_of_support_subset _ ((support_edgeDelta_flip_subset G c {v}).trans hE)
  have hRC : Disjoint R C := Finset.disjoint_left.mpr fun e heR heC =>
    let ⟨w, hw, hwe⟩ := Finset.mem_image.mp heR
    let ⟨_, _, hze⟩ := Finset.mem_image.mp heC
    G.ne_of_adj (hN.mem_toFinset.mp hw)
      (congrArg Prod.snd (hwe.trans hze.symm)).symm
  have hR : (∑ e ∈ R, edgeDelta G c (flip c {v}) e) =
      ∑ w ∈ N, edgeDelta G c (flip c {v}) (v, w) :=
    Finset.sum_image (fun a _ b _ h => congrArg Prod.snd h)
  have hC : (∑ e ∈ C, edgeDelta G c (flip c {v}) e) =
      ∑ w ∈ N, edgeDelta G c (flip c {v}) (w, v) :=
    Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h)
  rw [hsum, Finset.sum_union hRC, hR, hC]
  have hsymm : (∑ w ∈ N, edgeDelta G c (flip c {v}) (w, v)) =
      ∑ w ∈ N, edgeDelta G c (flip c {v}) (v, w) :=
    Finset.sum_congr rfl (fun w _ => edgeDelta_swap G c (flip c {v}) w v)
  have hdelta : ∀ w ∈ N, edgeDelta G c (flip c {v}) (v, w) =
      (if c w = c v then 1 else -1) := fun w hw =>
    let ha : G.Adj v w := hN.mem_toFinset.mp hw
    by simpa only [edgeDelta, cutIndicator, flip, Finset.mem_singleton,
      if_pos ha, if_pos rfl, if_pos True.intro, if_neg (G.ne_of_adj ha).symm]
      using bool_flip_indicator (c v) (c w)
  have hrow : (∑ w ∈ N, edgeDelta G c (flip c {v}) (v, w)) =
      ((N.filter fun w => c w = c v).card : ℤ) -
        ((N.filter fun w => c w ≠ c v).card : ℤ) := by
    rw [Finset.sum_congr rfl hdelta, Finset.sum_ite]
    simp [sub_eq_add_neg]
  rw [hsymm, hrow, two_mul]

/-- A strongly maximal coloring is canonically unfriendly at each allowed finite-degree vertex. -/
theorem unfriendlyAt_of_strongMaximal (G : SimpleGraph V) (A : Set V) (c : V → Bool)
    (hmax : StrongMaximal G A c) (v : V) (hv : v ∈ A)
    (hN : (G.neighborSet v).Finite) :
    UnfriendlyAt G (fun x => some (c x)) v := by
  classical
  have hg : gain G c {v} ≤ 0 := hmax {v}
    (fun x hx => (Finset.mem_singleton.mp hx).symm ▸ hv)
    (fun x hx => (Finset.mem_singleton.mp hx).symm ▸ hN)
  have hformula := gain_singleton G c v hN
  have hcounts : (hN.toFinset.filter fun w => c w = c v).card ≤
      (hN.toFinset.filter fun w => c w ≠ c v).card := by omega
  refine ⟨c v, rfl, ?_⟩
  rw [neighColored_card_eq G c v hN (c v), neighColored_card_eq G c v hN (!c v)]
  simp only [Bool.eq_not]
  exact Nat.cast_le.mpr hcounts

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlySparseHubTie.lean. -/
/-!
# Neutral low-vertex flips at monochromatic hub incidences

The low graph retains all vertices and only edges between two finite-degree
vertices. If a finite-degree vertex with sparse hub incidences is losing
in the full graph, its low-edge cut is tied and every hub incidence there
is monochromatic. Flipping it preserves low-graph strong maximality.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.SparseHubTie

open Energy
open scoped symmDiff

variable {V : Type u}

/-- Retain the low-low edges on the original vertex type. -/
def lowGraph (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (G.neighborSet x).Finite ∧ (G.neighborSet y).Finite
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

def hubNeighbors (G : SimpleGraph V) (x : V) : Set V :=
  G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}

theorem finite_lowGraph_neighbors (G : SimpleGraph V) (x : V) :
    ((lowGraph G).neighborSet x).Finite := by
  exact (Classical.em (G.neighborSet x).Finite).elim
    (fun hx => hx.subset fun _ h => h.1)
    (fun hx => Set.finite_empty.subset fun _ h => (hx h.2.1).elim)

private theorem gain_pos_of_bad (G : SimpleGraph V) (c : V → Bool) (x : V)
    (hx : (G.neighborSet x).Finite)
    (hbad : ¬ UnfriendlyAt G (fun v => some (c v)) x) : 0 < gain G c {x} := by
  apply lt_of_not_ge
  refine fun h => hbad
    (unfriendlyAt_of_strongMaximal G ({x} : Set V) c ?_ x (Set.mem_singleton x) hx)
  intro S hS _
  rcases Finset.subset_singleton_iff.mp
    (show S ⊆ {x} from fun _ hy => Finset.mem_singleton.mpr (hS hy)) with rfl | rfl <;> simp_all


/-- A neutral low flip preserves strong maximality on the low graph. -/
theorem strongMaximal_low_flip_of_zero (G : SimpleGraph V) (c : V → Bool) (x : V)
    (hc : StrongMaximal (lowGraph G) Set.univ c) (hz : gain (lowGraph G) c {x} = 0) :
    StrongMaximal (lowGraph G) Set.univ (flip c {x}) := by
  classical
  intro T _ hTf
  have h := hc ({x} ∆ T) (Set.subset_univ _) (fun z _ => finite_lowGraph_neighbors G z)
  rwa [gain_symmDiff (lowGraph G) c {x} T (fun z _ => finite_lowGraph_neighbors G z) hTf,
    hz, zero_add] at h

/-- Changing only hub coordinates preserves strong maximality on the low graph. -/
theorem strongMaximal_low_congr (G : SimpleGraph V) (c d : V → Bool)
    (hc : StrongMaximal (lowGraph G) Set.univ c)
    (hd : Set.EqOn d c {x | (G.neighborSet x).Finite}) :
    StrongMaximal (lowGraph G) Set.univ d := by
  intro S hS hSf
  exact (gain_congr_of_incident_eq (lowGraph G) d c S fun _ he =>
    ⟨hd he.1.2.1, hd he.1.2.2⟩).le.trans (hc S hS hSf)

private theorem tie_counts (ls lo hs ho : ℕ) (hbase : ls ≤ lo) (hloss : lo + ho < ls + hs)
    (hthin : hs + ho ≤ 1 ∨ hs + ho ≤ 2 ∧ Even (ls + lo + hs + ho)) :
    ls = lo ∧ 0 < hs ∧ ho = 0 := by
  rcases hthin with h | ⟨h, k, hk⟩ <;> omega

/-- At a losing low vertex the low cut is tied, and flipping the vertex
makes a nonempty set of hub edges crossing while losing none of them. -/
theorem low_tie_of_not_unfriendly (G : SimpleGraph V) (c : V → Bool) (x : V)
    (hx : (G.neighborSet x).Finite)
    (hthin : (hubNeighbors G x).ncard ≤ 1 ∨
      (hubNeighbors G x).ncard ≤ 2 ∧ Even (G.neighborSet x).ncard)
    (hmax : StrongMaximal (lowGraph G) Set.univ c)
    (hbad : ¬ UnfriendlyAt G (fun v => some (c v)) x) :
    gain (lowGraph G) c {x} = 0 ∧ (hubNeighbors G x).Nonempty ∧
      ∀ y ∈ hubNeighbors G x, c y = c x := by
  classical
  let L := (finite_lowGraph_neighbors G x).toFinset
  have hH : (hubNeighbors G x).Finite := hx.subset Set.inter_subset_left
  let H := hH.toFinset
  let N := hx.toFinset
  have hLmem (y : V) : y ∈ L ↔ G.Adj x y ∧ (G.neighborSet y).Finite :=
    (finite_lowGraph_neighbors G x).mem_toFinset.trans
      ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hx, h.2⟩⟩
  have hHmem (y : V) : y ∈ H ↔ G.Adj x y ∧ (G.neighborSet y).Infinite := hH.mem_toFinset
  have hd : Disjoint L H := Finset.disjoint_left.mpr
    fun y hyL hyH => ((hHmem y).mp hyH).2 ((hLmem y).mp hyL).2
  have hunion : N = L ∪ H := Finset.ext fun y =>
    hx.mem_toFinset.trans (by simp only [Finset.mem_union, hLmem, hHmem, ← and_or_left,
      Set.Infinite, em, and_true, SimpleGraph.mem_neighborSet])
  have hsplit (p : V → Prop) [DecidablePred p] :
      (N.filter p).card = (L.filter p).card + (H.filter p).card := by
    rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint
      (hd.mono (Finset.filter_subset ..) (Finset.filter_subset ..))]
  let same (y : V) := c y = c x
  let opp (y : V) := c y ≠ c x
  have card_sum (A : Finset V) : (A.filter same).card + (A.filter opp).card = A.card :=
    Finset.card_filter_add_card_filter_not (s := A) (p := same)
  have hbase := hmax {x} (Set.subset_univ _) (fun z _ => finite_lowGraph_neighbors G z)
  have hlow := gain_singleton (lowGraph G) c x (finite_lowGraph_neighbors G x)
  change gain (lowGraph G) c {x} = 2 * (((L.filter same).card : ℤ) -
    ((L.filter opp).card : ℤ)) at hlow
  have hpos := gain_pos_of_bad G c x hx hbad
  have hfull := gain_singleton G c x hx
  change gain G c {x} = 2 * (((N.filter same).card : ℤ) -
    ((N.filter opp).card : ℤ)) at hfull
  have hdiff : (L.filter opp).card + (H.filter opp).card <
      (L.filter same).card + (H.filter same).card := by
    have hs := hsplit same
    have ho := hsplit opp
    omega
  have hthin' : H.card ≤ 1 ∨ H.card ≤ 2 ∧ Even N.card := by
    simpa only [Set.ncard_eq_toFinset_card _ hH, Set.ncard_eq_toFinset_card _ hx] using hthin
  have hn : N.card = L.card + H.card := hunion ▸ Finset.card_union_of_disjoint hd
  rw [hn, ← card_sum L, ← card_sum H, ← Nat.add_assoc] at hthin'
  obtain ⟨heq, hsame, hopp⟩ := tie_counts _ _ _ _ (by omega) hdiff hthin'
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hsame
  refine ⟨by omega, ⟨z, hH.mem_toFinset.mp (Finset.mem_filter.mp hz).1⟩, ?_⟩
  exact fun y hy => Classical.byContradiction fun hne =>
    (Finset.card_ne_zero.mpr ⟨y, Finset.mem_filter.mpr ⟨hH.mem_toFinset.mpr hy, hne⟩⟩) hopp

end TenChallenges.Continuation.SparseHubTie

/- Inlined from Continuation/UnfriendlyInfiniteStability.lean. -/
/-!
# Infinite opposite neighborhoods and finite perturbations

On countable graphs, an infinite opposite-colored neighborhood guarantees the
canonical unfriendly inequality. At an infinite-degree vertex this condition is
also necessary. Finite flips away from the vertex preserve it.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped Cardinal

variable {V : Type u}

/-- Neighbors whose Boolean color is opposite to the vertex's color. -/
def oppositeSet (G : SimpleGraph V) (c : V → Bool) (v : V) : Set V :=
  {w | G.Adj v w ∧ c w ≠ c v}

lemma oppositeSet_eq_colored (G : SimpleGraph V) (c : V → Bool) (v : V) :
    oppositeSet G c v =
      G.neighborSet v ∩ (fun w => some (c w)) ⁻¹' {some (!(c v))} := by
  ext w
  simp [oppositeSet, Bool.eq_not]

/-- Infinitely many opponents ensure the unfriendly inequality on a countable graph. -/
theorem unfriendly_of_infinite_opposite [Countable V] (G : SimpleGraph V)
    (c : V → Bool) (v : V) (hO : (oppositeSet G c v).Infinite) :
    UnfriendlyAt G (fun w => some (c w)) v := by
  have : Infinite (NeighColored G (fun w => some (c w)) v (some (!(c v)))) :=
    Set.infinite_coe_iff.mpr ((oppositeSet_eq_colored G c v) ▸ hO)
  have : Countable (NeighColored G (fun w => some (c w)) v (some (c v))) :=
    inferInstanceAs (Countable {w : V // G.Adj v w ∧ some (c w) = some (c v)})
  exact ⟨c v, rfl, Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_le_mk _)⟩

/-- At any infinite-degree vertex, the unfriendly inequality forces infinitely many opponents. -/
theorem infinite_opposite_of_unfriendly (G : SimpleGraph V) (c : V → Bool) (v : V)
    (hN : (G.neighborSet v).Infinite) (hUF : UnfriendlyAt G (fun w => some (c w)) v) :
    (oppositeSet G c v).Infinite := by
  classical
  obtain ⟨b, hv, hcard⟩ := hUF
  obtain rfl : b = c v := (Option.some.inj hv).symm
  by_contra hO
  have hOfin : (oppositeSet G c v).Finite := Set.not_infinite.mp hO
  have : Finite (NeighColored G (fun w => some (c w)) v (some (!(c v)))) :=
    Set.finite_coe_iff.mpr ((oppositeSet_eq_colored G c v) ▸ hOfin)
  obtain ⟨e⟩ := (Cardinal.le_def ..).mp hcard
  have : Finite (NeighColored G (fun w => some (c w)) v (some (c v))) :=
    Finite.of_injective e e.injective
  have hSfin : (G.neighborSet v ∩ (fun w => some (c w)) ⁻¹' {some (c v)}).Finite :=
    Set.finite_coe_iff.mp
      (inferInstance : Finite (NeighColored G (fun w => some (c w)) v (some (c v))))
  exact hN ((hSfin.union hOfin).subset (fun w hw => (Classical.em (c w = c v)).elim
    (fun hc => Or.inl ⟨hw, congrArg some hc⟩) (fun hc => Or.inr ⟨hw, hc⟩)))

/-- A bad vertex in a countable graph has only finitely many opposite-colored neighbors. -/
theorem opposite_finite_of_not_unfriendly [Countable V] (G : SimpleGraph V)
    (c : V → Bool) (v : V) (hbad : ¬ UnfriendlyAt G (fun w => some (c w)) v) :
    (oppositeSet G c v).Finite :=
  Set.not_infinite.mp (fun hO => hbad (unfriendly_of_infinite_opposite G c v hO))

/-- A finite flip away from a vertex preserves its infinite opposite neighborhood. -/
theorem infinite_opposite_flip (G : SimpleGraph V) (c : V → Bool) (v : V)
    (S : Finset V) (hvS : v ∉ S) (hO : (oppositeSet G c v).Infinite) :
    (oppositeSet G (flip c S) v).Infinite := by
  classical
  have hsub : oppositeSet G c v \ (S : Set V) ⊆ oppositeSet G (flip c S) v :=
    fun w hw => ⟨hw.1.1, fun heq => hw.1.2
      ((if_neg hw.2).symm.trans (heq.trans (if_neg hvS)))⟩
  exact Set.Infinite.mono hsub (hO.sdiff S.finite_toSet)

/-- Unfriendliness at an infinite-degree vertex survives finite flips away from that vertex. -/
theorem unfriendly_infinite_flip [Countable V] (G : SimpleGraph V) (c : V → Bool)
    (v : V) (S : Finset V) (hvS : v ∉ S) (hN : (G.neighborSet v).Infinite)
    (hUF : UnfriendlyAt G (fun w => some (c w)) v) :
    UnfriendlyAt G (fun w => some (flip c S w)) v :=
  unfriendly_of_infinite_opposite G (flip c S) v
    (infinite_opposite_flip G c v S hvS (infinite_opposite_of_unfriendly G c v hN hUF))

private theorem neighbor_sdiff_opposite_subset_flip (G : SimpleGraph V) (c : V → Bool)
    (v : V) : G.neighborSet v \ oppositeSet G c v ⊆ oppositeSet G (flip c {v}) v := by
  classical
  intro w hw
  have hcw : c w = c v := Classical.byContradiction (fun hc => hw.2 ⟨hw.1, hc⟩)
  simpa [oppositeSet, flip, (G.ne_of_adj hw.1).symm, hcw] using hw.1

/-- Flipping a bad infinite-degree vertex gives it infinitely many opponents. -/
theorem infinite_opposite_flip_bad [Countable V] (G : SimpleGraph V) (c : V → Bool)
    (v : V) (hN : (G.neighborSet v).Infinite)
    (hbad : ¬ UnfriendlyAt G (fun w => some (c w)) v) :
    (oppositeSet G (flip c {v}) v).Infinite :=
  Set.Infinite.mono (neighbor_sdiff_opposite_subset_flip G c v)
    (hN.sdiff (opposite_finite_of_not_unfriendly G c v hbad))

/-- The newly repaired infinite-degree vertex stays unfriendly after finite-degree repairs. -/
theorem unfriendly_flip_bad_after_finite_degree_repair [Countable V] (G : SimpleGraph V)
    (c : V → Bool) (v : V) (S : Finset V)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite) (hN : (G.neighborSet v).Infinite)
    (hbad : ¬ UnfriendlyAt G (fun w => some (c w)) v) :
    UnfriendlyAt G (fun w => some (flip (flip c {v}) S w)) v :=
  unfriendly_of_infinite_opposite G (flip (flip c {v}) S) v
    (infinite_opposite_flip G (flip c {v}) v S (fun hvS => hN (hS v hvS))
      (infinite_opposite_flip_bad G c v hN hbad))

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlySignedSelection.lean. -/
/-!
# Permanent witnesses for signed constraints

The countable construction below assigns each vertex infinitely many distinct
neighbours meeting a prescribed Boolean response. Every witness is fixed when
it is selected, so the construction does not use preservation of an infinite
neighbourhood under a limit of recolourings.

This supplies the distinct-neighbour step used by `UnfriendlySignedMultigraph`.
The application to full-boundary cut profiles is formalized in
`UnfriendlyThreeBoundaryGraph`. No unrestricted unfriendly partition theorem
is proved here.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.SignedSelection

variable {V : Type u}

/-- Countably many vertices with infinitely many available neighbours allow
infinitely many permanent witnesses for any prescribed Boolean response. -/
theorem exists_response_coloring [Countable V] (R : V → V → Prop)
    (response : V → V → Bool → Bool)
    (hR : ∀ x, {y | R x y}.Infinite) :
    ∃ c : V → Bool, ∀ x, {y | R x y ∧ c y = response x y (c x)}.Infinite := by
  classical
  cases isEmpty_or_nonempty V
  · exact ⟨fun _ => false, fun x => isEmptyElim x⟩
  · have hfresh : ∀ (D F : Finset V) (x : V),
        ∃ y, R x y ∧ y ∉ D ∧ y ≠ x ∧ y ∉ F := fun D F x =>
      let ⟨y, hy, hyK⟩ := (hR x).exists_notMem_finset (D ∪ insert x F)
      ⟨y, hy, fun hyD => hyK (Finset.mem_union_left _ hyD),
        fun h => hyK (Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl h))),
        fun hyF => hyK (Finset.mem_union_right _ (Finset.mem_insert_of_mem hyF))⟩
    choose w hw using hfresh
    let : Encodable V := Encodable.ofCountable V
    -- Schedule every vertex together with every finite forbidden witness set.
    obtain ⟨e, he⟩ := exists_surjective_nat (V × Finset V)
    let s : ℕ → Finset V × (V → Bool) :=
      Nat.rec (∅, fun _ => false) (fun n state =>
        let x := (e n).1
        let y := w state.1 (e n).2 x
        (insert x (insert y state.1),
          Function.update state.2 y (response x y (state.2 x))))
    have hDstep : ∀ n, (s n).1 ⊆ (s (n + 1)).1 := fun n y hy =>
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy)
    have hDmono : Monotone (fun n => (s n).1) := monotone_nat_of_le_succ hDstep
    -- Once a vertex enters the domain, its colour never changes.
    have hcolstep : ∀ n y, y ∈ (s n).1 → (s (n + 1)).2 y = (s n).2 y :=
      fun n y hy => Function.update_of_ne
        (show y ≠ w (s n).1 (e n).2 (e n).1 from
          fun h => (hw (s n).1 (e n).2 (e n).1).2.1 (h ▸ hy)) _ _
    have hcoh : ∀ {m n : ℕ}, m ≤ n →
        ∀ y ∈ (s m).1, (s n).2 y = (s m).2 y := fun {m n} hmn =>
      Nat.le_induction
        (P := fun n _ => ∀ y ∈ (s m).1, (s n).2 y = (s m).2 y)
        (fun _ _ => rfl)
        (fun k hmk ih y hy => (hcolstep k y (hDmono hmk hy)).trans (ih y hy)) n hmn
    have htask : ∀ n, (e n).1 ∈ (s (n + 1)).1 := fun n => Finset.mem_insert_self _ _
    have hcover : ∀ x, ∃ n, x ∈ (s n).1 := fun x =>
      let ⟨n, hn⟩ := he (x, ∅)
      ⟨n + 1, Eq.mp (congrArg (fun x => x ∈ (s (n + 1)).1)
        (congrArg Prod.fst hn)) (htask n)⟩
    choose index hindom using hcover
    let c : V → Bool := fun x => (s (index x)).2 x
    have hc : ∀ n, ∀ x ∈ (s n).1, c x = (s n).2 x := fun n x hx =>
      (hcoh (Nat.le_max_right n (index x)) x (hindom x)).symm.trans
        (hcoh (Nat.le_max_left n (index x)) x hx)
    have hnewdom : ∀ n, w (s n).1 (e n).2 (e n).1 ∈ (s (n + 1)).1 :=
      fun n => Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hquery : ∀ n, c (e n).1 = (s n).2 (e n).1 := fun n =>
      (hc (n + 1) (e n).1 (htask n)).trans
        (Function.update_of_ne (hw (s n).1 (e n).2 (e n).1).2.2.1.symm _ _)
    have hnew : ∀ n, c (w (s n).1 (e n).2 (e n).1) =
        response (e n).1 (w (s n).1 (e n).2 (e n).1) (c (e n).1) := fun n =>
      ((hc (n + 1) _ (hnewdom n)).trans
        (Function.update_self (w (s n).1 (e n).2 (e n).1)
          (response (e n).1 (w (s n).1 (e n).2 (e n).1) ((s n).2 (e n).1))
          (s n).2)).trans
        (congrArg (response (e n).1 (w (s n).1 (e n).2 (e n).1)) (hquery n).symm)
    have hrequest : ∀ n, ∃ y, R (e n).1 y ∧
        c y = response (e n).1 y (c (e n).1) ∧ y ∉ (e n).2 := fun n =>
      ⟨w (s n).1 (e n).2 (e n).1, (hw (s n).1 (e n).2 (e n).1).1,
        hnew n, (hw (s n).1 (e n).2 (e n).1).2.2.2⟩
    have hreq : ∀ (x : V) (F : Finset V),
        ∃ y, R x y ∧ c y = response x y (c x) ∧ y ∉ F := fun x F =>
      let ⟨n, hn⟩ := he (x, F)
      Eq.mp (congrArg (fun t : V × Finset V =>
        ∃ y, R t.1 y ∧ c y = response t.1 y (c t.1) ∧ y ∉ t.2) hn) (hrequest n)
    -- A finite witness set is contradicted by the request forbidding that set.
    exact ⟨c, fun x hfin =>
      let ⟨y, hyR, hyc, hyF⟩ := hreq x hfin.toFinset
      hyF (hfin.mem_toFinset.mpr ⟨hyR, hyc⟩)⟩

/-- Prescribed colours can be retained when every other vertex has infinitely
many available neighbours outside the prescribed set. -/
theorem exists_response_coloring_eqOn [Countable V] (R : V → V → Prop)
    (response : V → V → Bool → Bool) (P : Set V) (p : V → Bool)
    (hR : ∀ x, x ∉ P → {y | R x y ∧ y ∉ P}.Infinite) :
    ∃ c : V → Bool, Set.EqOn c p P ∧
      ∀ x, x ∉ P → {y | R x y ∧ c y = response x y (c x)}.Infinite := by
  classical
  have hU : ∀ x : {x : V // x ∉ P}, {y : {y : V // y ∉ P} | R x.val y.val}.Infinite := by
    intro x
    apply Set.Infinite.of_image (Subtype.val : {x : V // x ∉ P} → V)
    exact (hR x.val x.property).mono fun y hy => ⟨⟨y, hy.2⟩, hy.1, rfl⟩
  obtain ⟨d, hd⟩ := exists_response_coloring
    (fun x y : {x : V // x ∉ P} => R x.val y.val)
    (fun x y b => response x.val y.val b) hU
  let c : V → Bool := fun x => if hx : x ∈ P then p x else d ⟨x, hx⟩
  have hc : ∀ x : {x : V // x ∉ P}, c x.val = d x := fun x => dif_neg x.property
  refine ⟨c, fun x hx => dif_pos hx, fun x hx => ?_⟩
  refine ((hd ⟨x, hx⟩).image (f := Subtype.val) (fun _ _ _ _ h => Subtype.ext h)).mono ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨hy.1, (hc y).trans (hy.2.trans
    (congrArg (response x y.val) (hc ⟨x, hx⟩).symm))⟩

private theorem signed_response_iff (a b s : Bool) :
    b = (a == s) ↔ (a == b) = s := by
  cases a <;> cases b <;> cases s <;> decide

/-- A signed relation with infinitely many distinct neighbours outside `P`
admits a colouring extending `p` with infinitely many satisfied requests at
each vertex outside `P`. A true sign asks for equal colours; false asks for
opposite colours. Parallel requests to the same neighbour are not counted
as distinct neighbours in this hypothesis or conclusion. -/
theorem exists_signed_coloring_eqOn [Countable V] (R : V → V → Prop)
    (sign : V → V → Bool) (P : Set V) (p : V → Bool)
    (hR : ∀ x, x ∉ P → {y | R x y ∧ y ∉ P}.Infinite) :
    ∃ c : V → Bool, Set.EqOn c p P ∧
      ∀ x, x ∉ P → {y | R x y ∧ (c x == c y) = sign x y}.Infinite := by
  obtain ⟨c, hcp, hc⟩ := exists_response_coloring_eqOn R (fun x y b => b == sign x y) P p hR
  exact ⟨c, hcp, fun x hx => (hc x hx).mono fun y hy =>
    ⟨hy.1, (signed_response_iff _ _ _).mp hy.2⟩⟩

end TenChallenges.Continuation.SignedSelection

/- Inlined from Continuation/UnfriendlySignedMultigraph.lean. -/
/-!
# Infinite satisfied degree in signed multigraphs

Edge identities are retained, and only the vertex type is assumed countable.
A parity of `false` requests equality; `true` requests opposite colours.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.SignedSelection

/-- A loopless multigraph whose edges request equality or opposition. -/
structure SignedMultiGraph (V : Type u) (E : Type v) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e
  parity : E → Bool

variable {V : Type u} {E : Type v}

/-- Toggle a colour exactly when the edge requests opposition. -/
def twist (b s : Bool) : Bool := if s then !b else b

private theorem twist_symm (a b s : Bool) : a = twist b s ↔ b = twist a s := by
  cases a <;> cases b <;> cases s <;> decide

private theorem twist_self (b : Bool) : twist b b = false := by
  cases b <;> rfl

private theorem infinite_bool_fiber {α : Type*} (s : Set α) (hs : s.Infinite)
    (f : α → Bool) : ∃ b, {e | e ∈ s ∧ f e = b}.Infinite := by
  have : Infinite s := Set.infinite_coe_iff.mpr hs
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber (fun e : s => f e.val)
  have := hb
  refine ⟨b, Set.infinite_of_injective_forall_mem
    (f := fun e : ((fun e : s => f e.val) ⁻¹' {b}) => e.val.val) ?_ ?_⟩
  · exact fun i j h => Subtype.ext (Subtype.ext h)
  · exact fun e => ⟨e.val.property, e.property⟩

namespace SignedMultiGraph

variable (M : SignedMultiGraph V E)

def Incident (x : V) (e : E) : Prop := M.left e = x ∨ M.right e = x

def Between (x y : V) : Set E :=
  {e | (M.left e = x ∧ M.right e = y) ∨ (M.left e = y ∧ M.right e = x)}

open Classical in
noncomputable def other (x : V) (e : E) : V :=
  if M.left e = x then M.right e else M.left e

def Satisfied (c : V → Bool) (e : E) : Prop :=
  c (M.left e) = twist (c (M.right e)) (M.parity e)

/-- Satisfied edges with both endpoints already frozen. -/
def witnesses (S : Set V) (c : V → Bool) (x : V) : Set E :=
  {e | M.Incident x e ∧ M.left e ∈ S ∧ M.right e ∈ S ∧ M.Satisfied c e}

def Admissible (P : Set V) (p : V → Bool) (S : Set V) (c : V → Bool) : Prop :=
  P ⊆ S ∧ Set.EqOn c p P ∧
    ∀ x ∈ S, x ∉ P → (M.witnesses S c x).Infinite

theorem incident_of_between {x y : V} {e : E} (he : e ∈ M.Between x y) :
    M.Incident x e :=
  he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)

theorem other_of_between {x y : V} {e : E} (he : e ∈ M.Between x y) :
    M.other x e = y := by
  classical
  rcases he with h | h
  · exact (if_pos h.1).trans h.2
  · exact (if_neg (fun hn => M.loopless e (hn.trans h.2.symm))).trans h.1

theorem between_other {x : V} {e : E} (he : M.Incident x e) :
    e ∈ M.Between x (M.other x e) := by
  classical
  rcases he with h | h
  · exact Or.inl ⟨h, (if_pos h).symm⟩
  · exact Or.inr ⟨(if_neg (fun hn => M.loopless e (hn.trans h.symm))).symm, h⟩

theorem endpoints_mem {S : Set V} {x : V} {e : E}
    (he : M.Incident x e) (hx : x ∈ S) (ho : M.other x e ∈ S) :
    M.left e ∈ S ∧ M.right e ∈ S := by
  classical
  rcases he with h | h
  · exact ⟨h.symm ▸ hx, (if_pos h : M.other x e = M.right e) ▸ ho⟩
  · exact ⟨(if_neg (fun hn => M.loopless e (hn.trans h.symm)) :
      M.other x e = M.left e) ▸ ho, h.symm ▸ hx⟩

theorem satisfied_iff_at (c : V → Bool) {x : V} {e : E} (he : M.Incident x e) :
    M.Satisfied c e ↔ c x = twist (c (M.other x e)) (M.parity e) := by
  classical
  rcases he with h | h
  · simp [Satisfied, other, h]
  · have hn : M.left e ≠ x := fun hn => M.loopless e (hn.trans h.symm)
    simpa only [Satisfied, other, if_neg hn, h] using
      twist_symm (c (M.left e)) (c x) (M.parity e)

theorem witnesses_mono {S T : Set V} {c d : V → Bool}
    (hST : S ⊆ T) (hdc : Set.EqOn d c S) (x : V) :
    M.witnesses S c x ⊆ M.witnesses T d x := by
  rintro e ⟨he, hL, hR, hs⟩
  refine ⟨he, hST hL, hST hR, ?_⟩
  simpa only [Satisfied, hdc hL, hdc hR] using hs

private theorem admissible_extend {P S T : Set V} {p q d : V → Bool}
    (hq : M.Admissible P p S q) (hST : S ⊆ T) (hdq : Set.EqOn d q S)
    (hnew : ∀ x ∈ T, x ∉ S → (M.witnesses T d x).Infinite) :
    M.Admissible P p T d := by
  refine ⟨hq.1.trans hST, fun x hx => (hdq (hq.1 hx)).trans (hq.2.1 hx), ?_⟩
  intro x hx hxP
  by_cases hxS : x ∈ S
  · exact (hq.2.2 x hxS hxP).mono (M.witnesses_mono hST hdq x)
  · exact hnew x hx hxS

private theorem exists_maximal_admissible (P : Set V) (p : V → Bool) :
    ∃ (S : Set V) (q : V → Bool), M.Admissible P p S q ∧
      ∀ (T : Set V) (q' : V → Bool), M.Admissible P p T q' → S ⊆ T →
        Set.EqOn q' q S → T ⊆ S := by
  classical
  let T : Type u := {a : Set V × (V → Bool) // M.Admissible P p a.1 a.2}
  let r : T → T → Prop := fun a b =>
    a.1.1 ⊆ b.1.1 ∧ Set.EqOn b.1.2 a.1.2 a.1.1
  have htrans : ∀ {a b c : T}, r a b → r b c → r a c := fun {a b c} hab hbc =>
    ⟨hab.1.trans hbc.1, fun y hy => (hbc.2 (hab.1 hy)).trans (hab.2 hy)⟩
  have hchain : ∀ C : Set T, IsChain r C → ∃ ub, ∀ a ∈ C, r a ub := by
    intro C hC
    let dom : Set V := P ∪ ⋃ a ∈ C, a.1.1
    let col : V → Bool := fun y =>
      if h : ∃ a ∈ C, y ∈ a.1.1 then (Classical.choose h).1.2 y else p y
    have hcol : ∀ a ∈ C, Set.EqOn col a.1.2 a.1.1 := by
      intro a ha y hy
      have h : ∃ a ∈ C, y ∈ a.1.1 := ⟨a, ha, hy⟩
      have hs := Classical.choose_spec h
      have hv : col y = (Classical.choose h).1.2 y := dif_pos h
      rw [hv]
      by_cases heq : Classical.choose h = a
      · rw [heq]
      · rcases hC hs.1 ha heq with hle | hle
        · exact (hle.2 hs.2).symm
        · exact hle.2 hy
    have hP : Set.EqOn col p P := fun y hy =>
      if h : ∃ a ∈ C, y ∈ a.1.1 then
        (dif_pos h).trans ((Classical.choose h).property.2.1 hy)
      else dif_neg h
    have hAdm : M.Admissible P p dom col := by
      refine ⟨Set.subset_union_left, hP, ?_⟩
      intro x hx hxP
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hx.resolve_left hxP)
      exact (a.property.2.2 x hxa hxP).mono (M.witnesses_mono (T := dom)
        (fun y hy => Or.inr (Set.mem_iUnion₂.mpr ⟨a, ha, hy⟩)) (hcol a ha) x)
    exact ⟨⟨(dom, col), hAdm⟩, fun a ha =>
      ⟨fun y hy => Or.inr (Set.mem_iUnion₂.mpr ⟨a, ha, hy⟩), hcol a ha⟩⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hchain htrans
  exact ⟨m.1.1, m.1.2, m.property, fun S q' hAdm hsub hfix =>
    (hm ⟨(S, q'), hAdm⟩ ⟨hsub, hfix⟩).1⟩

private theorem extend_to_frozen (P S : Set V) (p q : V → Bool)
    (hq : M.Admissible P p S q) (x : V) (hx : x ∉ S)
    (hi : {e | M.Incident x e ∧ M.other x e ∈ S}.Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ M.Admissible P p (S ∪ {x}) q' := by
  classical
  obtain ⟨b, hb⟩ := infinite_bool_fiber _ hi
    (fun e => twist (q (M.other x e)) (M.parity e))
  let q' : V → Bool := Function.update q x b
  have hfix : Set.EqOn q' q S := fun y hy =>
    Function.update_of_ne (show y ≠ x from fun h => hx (h ▸ hy)) _ _
  have hxval : q' x = b := Function.update_self ..
  have hnew : (M.witnesses (S ∪ {x}) q' x).Infinite := hb.mono fun e he =>
    let hends := M.endpoints_mem he.1.1 (Or.inr rfl) (Or.inl he.1.2 :
      M.other x e ∈ S ∪ {x})
    ⟨he.1.1, hends.1, hends.2, (M.satisfied_iff_at q' he.1.1).mpr
      (hxval.trans (he.2.symm.trans
        (congrArg (fun b => twist b (M.parity e)) (hfix he.1.2)).symm))⟩
  refine ⟨q', hfix, M.admissible_extend hq Set.subset_union_left hfix ?_⟩
  rintro v (hv | rfl) hnot
  · exact (hnot hv).elim
  · exact hnew

private theorem extend_parallel (P S : Set V) (p q : V → Bool)
    (hq : M.Admissible P p S q) (x y : V) (hx : x ∉ S) (hy : y ∉ S)
    (hi : (M.Between x y).Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ M.Admissible P p (S ∪ {x, y}) q' := by
  classical
  have hxy : x ≠ y := fun h =>
    let ⟨e, he⟩ := hi.nonempty
    he.elim (fun he => M.loopless e (he.1.trans (h.trans he.2.symm)))
      (fun he => M.loopless e (he.1.trans (h.symm.trans he.2.symm)))
  obtain ⟨b, hb⟩ := infinite_bool_fiber _ hi M.parity
  let q' : V → Bool := Function.update (Function.update q x false) y b
  let T : Set V := S ∪ {x, y}
  have hfix : Set.EqOn q' q S := fun v hv =>
    (Function.update_of_ne (show v ≠ y from fun h => hy (h ▸ hv)) _ _).trans
      (Function.update_of_ne (show v ≠ x from fun h => hx (h ▸ hv)) _ _)
  have hqx : q' x = false := (Function.update_of_ne hxy _ _).trans (Function.update_self ..)
  have hqy : q' y = b := Function.update_self ..
  have hends : ∀ e, e ∈ M.Between x y → M.left e ∈ T ∧ M.right e ∈ T :=
    fun e he => M.endpoints_mem (M.incident_of_between he)
      (show x ∈ T from Or.inr (Or.inl rfl))
      (Eq.mp (congrArg (fun v => v ∈ T) (M.other_of_between he).symm)
        (show y ∈ T from Or.inr (Or.inr rfl)))
  have hsat : ∀ e, e ∈ M.Between x y ∧ M.parity e = b → M.Satisfied q' e :=
    fun e he => (M.satisfied_iff_at q' (M.incident_of_between he.1)).mpr
      (hqx.trans ((twist_self b).symm.trans (congrArg₂ twist
        ((congrArg q' (M.other_of_between he.1)).trans hqy).symm he.2.symm)))
  have hnewx : (M.witnesses T q' x).Infinite := hb.mono fun e he =>
    ⟨M.incident_of_between he.1, (hends e he.1).1, (hends e he.1).2, hsat e he⟩
  have hnewy : (M.witnesses T q' y).Infinite := hb.mono fun e he =>
    ⟨he.1.elim (fun he => Or.inr he.2) (fun he => Or.inl he.1),
      (hends e he.1).1, (hends e he.1).2, hsat e he⟩
  refine ⟨q', hfix, M.admissible_extend hq Set.subset_union_left hfix ?_⟩
  rintro v (hv | rfl | rfl) hnot
  · exact (hnot hv).elim
  · exact hnewx
  · exact hnewy

private theorem residual_neighbors (S : Set V)
    (hdeg : ∀ x, x ∉ S → {e | M.Incident x e}.Infinite)
    (hinto : ∀ x, x ∉ S → {e | M.Incident x e ∧ M.other x e ∈ S}.Finite)
    (hpair : ∀ x, x ∉ S → ∀ y, y ∉ S → (M.Between x y).Finite) :
    ∀ x, x ∉ S → {y | y ∉ S ∧ (M.Between x y).Nonempty}.Infinite := by
  intro x hx hfin
  have hi := (hdeg x hx).sdiff (hinto x hx)
  have hf := hfin.biUnion (fun y hy => hpair x hx y hy.1)
  exact hi (hf.subset fun e he => Set.mem_iUnion₂.mpr
    ⟨M.other x e, ⟨(fun ho => he.2 ⟨he.1, ho⟩), e, M.between_other he.1⟩,
      M.between_other he.1⟩)

private theorem complete_residual [Countable V] (P S : Set V) (p q : V → Bool)
    (hq : M.Admissible P p S q)
    (hres : ∀ x, x ∉ S → {y | y ∉ S ∧ (M.Between x y).Nonempty}.Infinite) :
    ∃ c : V → Bool, Set.EqOn c p P ∧
      ∀ x, x ∉ P → {e | M.Incident x e ∧ M.Satisfied c e}.Infinite := by
  classical
  let response : V → V → Bool → Bool := fun x y b =>
    if h : (M.Between x y).Nonempty then twist b (M.parity (Classical.choose h)) else b
  obtain ⟨c, hcS, hc⟩ := exists_response_coloring_eqOn
    (fun x y => (M.Between x y).Nonempty) response S q
    (fun x hx => (hres x hx).mono fun y hy => ⟨hy.2, hy.1⟩)
  refine ⟨c, fun x hx => (hcS (hq.1 hx)).trans (hq.2.1 hx), fun x hxP => ?_⟩
  by_cases hxS : x ∈ S
  · exact ((hq.2.2 x hxS hxP).mono
      (M.witnesses_mono (Set.subset_univ S) hcS x)).mono fun e he =>
        ⟨he.1, he.2.2.2⟩
  · let Y : Set V := {y | (M.Between x y).Nonempty ∧ c y = response x y (c x)}
    have : Infinite Y := Set.infinite_coe_iff.mpr (hc x hxS)
    have hinj : Function.Injective (fun y : Y => Classical.choose y.property.1) :=
      fun y z heq => Subtype.ext
        ((M.other_of_between (Classical.choose_spec y.property.1)).symm.trans
          ((congrArg (M.other x) heq).trans
            (M.other_of_between (Classical.choose_spec z.property.1))))
    have hresponse : ∀ y : Y, c y.val =
        twist (c x) (M.parity (Classical.choose y.property.1)) := fun y =>
      y.property.2.trans (dif_pos y.property.1)
    have hsat : ∀ y : Y, M.Satisfied c (Classical.choose y.property.1) := fun y =>
      (M.satisfied_iff_at c (M.incident_of_between
        (Classical.choose_spec y.property.1))).mpr
        ((twist_symm _ _ _).mpr
          ((congrArg c (M.other_of_between
            (Classical.choose_spec y.property.1))).trans (hresponse y)))
    exact Set.infinite_of_injective_forall_mem hinj fun y =>
      ⟨M.incident_of_between (Classical.choose_spec y.property.1), hsat y⟩

/-- Prescribed colours extend so that every other vertex satisfies infinitely
many incident edge identities. No countability assumption on the edge type is needed. -/
theorem exists_infinitely_satisfied_extension [Countable V]
    (P : Set V) (p : V → Bool)
    (hdeg : ∀ x, x ∉ P → {e | M.Incident x e}.Infinite) :
    ∃ c : V → Bool, Set.EqOn c p P ∧
      ∀ x, x ∉ P → {e | M.Incident x e ∧ M.Satisfied c e}.Infinite := by
  classical
  obtain ⟨S, q, hq, hmax⟩ := M.exists_maximal_admissible P p
  have hinto : ∀ x, x ∉ S →
      {e | M.Incident x e ∧ M.other x e ∈ S}.Finite := fun x hx =>
    Set.not_infinite.mp fun hi =>
      let ⟨q', hfix, hnew⟩ := M.extend_to_frozen P S p q hq x hx hi
      hx (hmax (S ∪ {x}) q' hnew Set.subset_union_left hfix (Or.inr rfl))
  have hpair : ∀ x, x ∉ S → ∀ y, y ∉ S → (M.Between x y).Finite :=
    fun x hx y hy => Set.not_infinite.mp fun hi =>
      let ⟨q', hfix, hnew⟩ := M.extend_parallel P S p q hq x y hx hy hi
      hx (hmax (S ∪ {x, y}) q' hnew Set.subset_union_left hfix (Or.inr (Or.inl rfl)))
  exact M.complete_residual P S p q hq
    (M.residual_neighbors S
      (fun x hx => hdeg x (fun hxP => hx (hq.1 hxP))) hinto hpair)

end SignedMultiGraph
end TenChallenges.Continuation.SignedSelection

/- Inlined from Continuation/UnfriendlySparseHubPalette.lean. -/
/-!
# Extending prescribed colours at finite-degree vertices

Each infinite-degree vertex can receive infinitely many opponents while every
finite-degree vertex keeps its prescribed colour.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.SparseHubPalette

open SignedSelection

variable {V : Type u}

/-- Choose the hub colours while retaining all prescribed finite-degree colours. -/
theorem exists_palette [Countable V] (G : SimpleGraph V) (c₀ : V → Bool) :
    ∃ c : V → Bool, Set.EqOn c c₀ {v | (G.neighborSet v).Finite} ∧
      ∀ v, (G.neighborSet v).Infinite → (Energy.oppositeSet G c v).Infinite := by
  let E := {xy : V × V // G.Adj xy.1 xy.2}
  let M : SignedMultiGraph V E :=
    { left := fun e => e.val.1
      right := fun e => e.val.2
      loopless := fun e => G.ne_of_adj e.property
      parity := fun _ => true }
  let P : Set V := {v | (G.neighborSet v).Finite}
  have hdeg (x : V) (hx : x ∉ P) : {e | M.Incident x e}.Infinite :=
    fun hf => hx ((hf.image M.right).subset fun y hy =>
      ⟨⟨(x, y), hy⟩, Or.inl rfl, rfl⟩)
  obtain ⟨c, hcP, hc⟩ := M.exists_infinitely_satisfied_extension P c₀ hdeg
  refine ⟨c, hcP, fun x hx hf => ?_⟩
  have hpairs := (hf.image (Prod.mk x)).union (hf.image (fun y => (y, x)))
  apply hc x hx
  apply (hpairs.preimage (Subtype.val_injective (p := fun xy : V × V => G.Adj xy.1 xy.2)).injOn).subset
  rintro ⟨⟨y, z⟩, hyz⟩ ⟨hinc, hsat⟩
  have hne : c y ≠ c z := Bool.eq_not.mp (show c y = !c z from hsat)
  rcases (show y = x ∨ z = x from hinc) with rfl | rfl
  · exact Or.inl ⟨z, ⟨hyz, hne.symm⟩, rfl⟩
  · exact Or.inr ⟨y, ⟨hyz.symm, hne⟩, rfl⟩

end TenChallenges.Continuation.SparseHubPalette

/- Inlined from Continuation/UnfriendlyFromGlobal.lean. -/
set_option autoImplicit false


namespace TenChallenges.Continuation

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- An extension unfriendly at the queried vertex admits a finite consistent response. -/
theorem finite_response_of_unfriendly_partition (p : V → Option Bool)
    (f : V → Option Bool) (hf : HasFiniteDomain f) (hfp : Extends f p)
    (v : V) (hp : UnfriendlyAt G p v) :
    ∃ g, IsLegalResponse G f g v ∧ Extends g p := by
  classical
  obtain ⟨b, hpv, hcard⟩ := hp
  let S : Set V := G.neighborSet v ∩ f ⁻¹' {some b}
  have hS : S.Finite := hf.subset
    (fun _ hx => Option.ne_none_iff_exists'.mpr ⟨b, hx.2⟩)
  have hsub : S ⊆ G.neighborSet v ∩ p ⁻¹' {some b} :=
    fun x hx => ⟨hx.1, hfp x b hx.2⟩
  obtain ⟨e⟩ := (Cardinal.le_def S (NeighColored G p v (some (!b)))).mp
    ((Cardinal.mk_le_mk_of_subset hsub).trans hcard)
  let : Finite S := hS.to_subtype
  let T : Set V := Set.range fun x : S => (e x).1
  have hT : T.Finite := Set.finite_range _
  have hTc : ∀ x ∈ T, p x = some (!b) :=
    fun _ ⟨y, hy⟩ => hy ▸ (e y).2.2
  let g : V → Option Bool := fun x => if x = v ∨ x ∈ T then p x else f x
  have hfg : Extends f g := fun x c hc =>
    if h : x = v ∨ x ∈ T then (if_pos h).trans (hfp x c hc)
    else (if_neg h).trans hc
  have hgp : Extends g p := fun x c hc =>
    if h : x = v ∨ x ∈ T then (if_pos h).symm.trans hc
    else hfp x c ((if_neg h).symm.trans hc)
  have hgf : HasFiniteDomain g := (hf.union ((Set.finite_singleton v).union hT)).subset
    fun x hx => if h : x = v ∨ x ∈ T then Or.inr h else Or.inl
      (fun hn => hx ((if_neg h).trans hn))
  have hsame : (G.neighborSet v ∩ g ⁻¹' {some b}) ⊆ S := fun x hx =>
    ⟨hx.1, if h : x = v ∨ x ∈ T then h.elim
      (fun hv => False.elim (G.irrefl (hv ▸ hx.1)))
      (fun ht => False.elim ((Bool.not_eq_self b).mp (Option.some.inj
        ((hTc x ht).symm.trans ((if_pos h).symm.trans hx.2)))))
    else (if_neg h).symm.trans hx.2⟩
  let E : S ↪ NeighColored G g v (some (!b)) :=
    ⟨fun s => ⟨(e s).1, (e s).2.1,
      (if_pos (Or.inr ⟨s, rfl⟩)).trans (e s).2.2⟩,
      fun s t h => e.injective (Subtype.ext
        (congrArg (fun z : NeighColored G g v (some (!b)) => z.val) h))⟩
  exact ⟨g, ⟨hfg, hgf, b, (if_pos (Or.inl rfl)).trans hpv,
    (Cardinal.mk_le_mk_of_subset hsame).trans ((Cardinal.le_def ..).mpr ⟨E⟩)⟩, hgp⟩

/-- Finite partial partitions consistent with a global unfriendly partition
win at every clock. -/
theorem wins_from_unfriendly_partition (p : V → Option Bool)
    (hp : ∀ v, UnfriendlyAt G p v) :
    ∀ (α : Ordinal.{v}) (f : V → Option Bool),
      HasFiniteDomain f → Extends f p → PartitionerWins G f α := by
  intro α
  induction α using WellFoundedLT.induction
  rename_i α ih
  intro f hf hfp
  rw [PartitionerWins]
  exact fun x β hβ =>
    let ⟨g, hg, hgp⟩ := finite_response_of_unfriendly_partition G p f hf hfp x (hp x)
    ⟨g, hg, ih β hβ g hg.2.1 hgp⟩

/-- A global unfriendly partition gives Partitioner a winning strategy at every ordinal clock. -/
theorem partitionerWins_of_unfriendly_partition (p : V → Option Bool)
    (hp : ∀ v, UnfriendlyAt G p v) (α : Ordinal.{v}) :
    PartitionerWins G (emptyPartition V) α := by
  have hf : HasFiniteDomain (emptyPartition V) := by simp [HasFiniteDomain, emptyPartition]
  exact wins_from_unfriendly_partition G p hp α (emptyPartition V) hf
    (fun _ b h => False.elim (Option.some_ne_none b h.symm))

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlySparseIncidence.lean. -/
/-!
# Unfriendly partitions with sparse incidence at finite-degree vertices

The graph between finite-degree vertices and the graph between hubs may both
be arbitrary. At each finite-degree vertex we allow one hub neighbour, or two
when the vertex has even degree.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.SparseIncidence

open Energy SparseHubTie

variable {V : Type u} (G : SimpleGraph V)

private abbrev Incidence := {e : V × V // (G.neighborSet e.1).Infinite ∧ G.Adj e.1 e.2}

private def crossing (c : V → Bool) : Set (Incidence G) :=
  {e | c e.val.2 ≠ c e.val.1}

private theorem crossing_after_flip (c : V → Bool) (x : V) (hx : (G.neighborSet x).Finite)
    (hne : (hubNeighbors G x).Nonempty) (hsame : ∀ y ∈ hubNeighbors G x, c y = c x) :
    crossing G c ⊂ crossing G (flip c {x}) := by
  classical
  have hh {y : V} (hy : (G.neighborSet y).Infinite) : y ≠ x := fun h => hy (h ▸ hx)
  constructor
  · intro e he
    have hdst : e.val.2 ≠ x := fun h => he ((hsame e.val.1 ⟨h ▸ e.property.2.symm, e.property.1⟩).symm ▸ congrArg c h)
    simpa only [crossing, Set.mem_ofPred_eq, Energy.flip, Finset.mem_singleton, if_neg hdst, if_neg (hh e.property.1)] using he
  obtain ⟨y, hy⟩ := hne
  let e : Incidence G := ⟨(y, x), hy.2, hy.1.symm⟩
  have hnew : e ∈ crossing G (Energy.flip c {x}) := by
    change Energy.flip c {x} x ≠ Energy.flip c {x} y
    simp [Energy.flip, hh hy.2, hsame y hy]
  intro h
  exact (h hnew) (hsame y hy).symm

/-- Every countable graph satisfying the sparse incidence condition has an
unfriendly colouring strongly maximal for the edges between finite-degree vertices. -/
theorem exists_unfriendly_of_sparse_hub_incidence [Countable V]
    (hthin : ∀ x, (G.neighborSet x).Finite →
      (hubNeighbors G x).ncard ≤ 1 ∨ (hubNeighbors G x).ncard ≤ 2 ∧ Even (G.neighborSet x).ncard) :
    ∃ c : V → Bool, StrongMaximal (lowGraph G) Set.univ c ∧
      ∀ x, UnfriendlyAt G (fun v => some (c v)) x := by
  classical
  let : TopologicalSpace Bool := ⊥
  let : DiscreteTopology Bool := ⟨rfl⟩
  let K : Set (V → Bool) := {c | StrongMaximal (lowGraph G) Set.univ c}
  have hK : IsCompact K := (StrongTopology.isClosed_strongMaximal (lowGraph G) Set.univ).isCompact
  obtain ⟨p, _, hp⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn (lowGraph G) ∅ (fun _ => false)
  obtain ⟨q, hqp, hgood⟩ := SparseHubPalette.exists_palette G p
  have hq : q ∈ K := strongMaximal_low_congr G p q (by simpa using hp) hqp
  have hclosed (e : Incidence G) : IsClosed {c | e ∈ crossing G c} := by
    change IsClosed ((fun c : V → Bool => (c e.val.2, c e.val.1)) ⁻¹' {b : Bool × Bool | b.1 ≠ b.2})
    exact (isClosed_discrete _).preimage (by fun_prop)
  obtain ⟨c, hc, hqc, hmax⟩ := MaximalWitnesses.exists_maximal_witnesses hK (crossing G) hclosed hq
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : (G.neighborSet x).Finite
  · by_contra hbad
    obtain ⟨hz, hn, hs⟩ := low_tie_of_not_unfriendly G c x hx (hthin x hx) hc hbad
    have hlt := crossing_after_flip G c x hx hn hs
    exact hlt.not_ge (hmax _ (strongMaximal_low_flip_of_zero G c x hc hz) hlt.le)
  apply unfriendly_of_infinite_opposite G c x
  apply (hgood x hx).mono
  rintro y ⟨hxy, hne⟩
  exact ⟨hxy, hqc (show (⟨(x, y), hx, hxy⟩ : Incidence G) ∈ crossing G q from hne)⟩

/-- Every ordinal clock is won under the same incidence condition. -/
theorem all_clocks_of_sparse_hub_incidence [Countable V]
    (hthin : ∀ x, (G.neighborSet x).Finite →
      (hubNeighbors G x).ncard ≤ 1 ∨ (hubNeighbors G x).ncard ≤ 2 ∧ Even (G.neighborSet x).ncard) :
    ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by
  obtain ⟨c, _, hc⟩ := exists_unfriendly_of_sparse_hub_incidence G hthin
  exact partitionerWins_of_unfriendly_partition G (fun x => some (c x)) hc

end TenChallenges.Continuation.SparseIncidence

theorem solution {V : Type u} [Countable V] (G : SimpleGraph V)
    (hthin : ∀ x, (G.neighborSet x).Finite →
      (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).ncard ≤ 1 ∨
        (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).ncard ≤ 2 ∧
          Even (G.neighborSet x).ncard) :
    ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r :=
  TenChallenges.Continuation.SparseIncidence.all_clocks_of_sparse_hub_incidence G hthin

#print axioms solution
