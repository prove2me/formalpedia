-- Prove2me | solution 1 for TenChallenges.challenge_10_boundedLossCells
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:56:59.086481+00:00
-- url     : https://prove2.me/submissions/9c824363-1184-41e5-99b2-211b5851d914

import Definitions.Def_TenChallenges_Challenge_10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Function.DependsOn
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete

universe u w v

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

/- Inlined from Continuation/UnfriendlyFiniteRepair.lean. -/
set_option autoImplicit false


namespace TenChallenges.Continuation.FiniteRepair

open scoped symmDiff

/-- A bounded integer cut gain attains a finite flip after which no allowed flip improves it. -/
theorem exists_stable_flip {V : Type u} [DecidableEq V] {C : Type v}
    (allowed : Finset V → Prop) (hempty : allowed ∅)
    (hclosed : ∀ s t, allowed s → allowed t → allowed (s ∆ t))
    (flip : C → Finset V → C) (gain : C → Finset V → ℤ)
    (hcocycle : ∀ c s t, allowed s → allowed t →
      gain c (s ∆ t) = gain c s + gain (flip c s) t)
    (c : C) (B : ℤ) (hbound : ∀ s, allowed s → gain c s ≤ B) :
    ∃ s, allowed s ∧ ∀ t, allowed t → gain (flip c s) t ≤ 0 := by
  obtain ⟨m, ⟨s, hs, hsm⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ s, allowed s ∧ gain c s = z)
    ⟨B, fun z ⟨s, hs, hz⟩ => hz ▸ hbound s hs⟩
    ⟨gain c ∅, ∅, hempty, rfl⟩
  refine ⟨s, hs, ?_⟩
  intro t ht
  have hle := hmax (gain c (s ∆ t)) ⟨s ∆ t, hclosed s t hs ht, rfl⟩
  rw [hcocycle c s t hs ht, hsm] at hle
  exact (add_le_iff_nonpos_right _).mp hle

end TenChallenges.Continuation.FiniteRepair

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

/- Inlined from Continuation/UnfriendlyLimit.lean. -/
set_option autoImplicit false


namespace TenChallenges.Continuation

open scoped Cardinal

variable {V : Type u} [Countable V] (G : SimpleGraph V)

/-- Finite witnesses suffice for the cardinal majority inequality on a countable graph. -/
theorem unfriendlyAt_of_finite_approximations (p : V → Option Bool) (v : V) (b : Bool)
    (hpv : p v = some b)
    (ha : ∀ s : Finset V,
      (∀ x ∈ s, G.Adj v x ∧ p x = some b) →
      ∃ f : V → Option Bool, Extends f p ∧ UnfriendlyAt G f v ∧
        ∀ x ∈ s, f x = some b) :
    UnfriendlyAt G p v := by
  classical
  refine ⟨b, hpv, ?_⟩
  by_cases hO : (G.neighborSet v ∩ p ⁻¹' {some (!b)}).Finite
  · let : Fintype (NeighColored G p v (some (!b))) := hO.fintype
    rw [Cardinal.mk_fintype (NeighColored G p v (some (!b)))]
    apply Cardinal.mk_le_iff_forall_finset_subset_card_le.mpr
    intro s hs
    obtain ⟨f, hfp, ⟨c, hfv, hc⟩, hsf⟩ := ha s (fun x hx => hs hx)
    have hcb : c = b := Option.some.inj ((hfp v c hfv).symm.trans hpv)
    subst c
    have hle : #(s : Set V) ≤ #(NeighColored G p v (some (!b))) :=
      (Cardinal.mk_le_mk_of_subset (show (s : Set V) ⊆
        G.neighborSet v ∩ f ⁻¹' {some b} from
          fun x hx => ⟨(hs hx).1, hsf x hx⟩)).trans
        (hc.trans (Cardinal.mk_le_mk_of_subset
          (fun x hx => ⟨hx.1, hfp x (!b) hx.2⟩)))
    change (#↥s : Cardinal.{u}) ≤ #(NeighColored G p v (some (!b))) at hle
    rw [Cardinal.mk_coe_finset] at hle
    simpa only [Cardinal.mk_fintype, Nat.cast_le] using hle
  · have : Infinite (NeighColored G p v (some (!b))) := Set.infinite_coe_iff.mpr hO
    have : Countable (NeighColored G p v (some b)) :=
      inferInstanceAs (Countable {x : V // G.Adj v x ∧ p x = some b})
    exact Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_le_mk _)

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyPersistent.lean. -/
/-!
# Persistent winning states in the unfriendly partition game

A state winning at every ordinal clock in the vertex universe admits, for every
query, a finite legal response that is again winning at every clock. This is a
structural consequence of the supremum of the losing clocks of all responses.
It does not assert that the empty coloring is a persistent state.
-/


namespace TenChallenges.Continuation

variable {V : Type u} (G : SimpleGraph V)

/-- A winning state at every clock in the universe of its vertex type. -/
def Persistent (f : V → Option Bool) : Prop :=
  ∀ α : Ordinal.{u}, PartitionerWins G f α

private theorem wins_mono {f : V → Option Bool} {α β : Ordinal.{v}}
    (hβα : β ≤ α) (h : PartitionerWins G f α) : PartitionerWins G f β := by
  rw [PartitionerWins] at h ⊢
  exact fun x γ hγ => h x γ (hγ.trans_le hβα)

/-- Every query from a persistent state has a persistent finite legal response. -/
theorem persistent_response {f : V → Option Bool} (hf : Persistent G f) (x : V) :
    ∃ g, IsLegalResponse G f g x ∧ Persistent G g := by
  classical
  by_contra h
  have hbad : ∀ g : {g : V → Option Bool // IsLegalResponse G f g x},
      ∃ α : Ordinal.{u}, ¬ PartitionerWins G g.val α := fun g =>
    not_forall.mp (show ¬ Persistent G g.val from fun hg => h ⟨g.val, g.property, hg⟩)
  choose α hα using hbad
  let β : Ordinal.{u} := ⨆ g, α g
  have hw : PartitionerWins G f (Order.succ β) := hf _
  rw [PartitionerWins] at hw
  obtain ⟨g, hg, hwin⟩ := hw x β (Order.lt_succ β)
  exact hα ⟨g, hg⟩ (wins_mono G (Ordinal.le_iSup α ⟨g, hg⟩) hwin)

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyPlay.lean. -/
/-!
# Fair play from a persistent unfriendly-partition state

On a countable graph, persistence of the empty state supplies an increasing chain
of partial colorings that covers every vertex and makes each vertex unfriendly
at arbitrarily late stages.
-/


namespace TenChallenges.Continuation

variable {V : Type u} (G : SimpleGraph V)

/-- A persistent empty state admits a fair infinite legal play on a countable graph. -/
theorem persistent_fair_play [Countable V] (h : Persistent G (emptyPartition V)) :
    ∃ f : ℕ → (V → Option Bool),
      (∀ n, Extends (f n) (f (n + 1))) ∧
      (∀ v, ∃ n b, f n v = some b) ∧
      (∀ v N, ∃ n, N ≤ n ∧ UnfriendlyAt G (f n) v) := by
  classical
  cases isEmpty_or_nonempty V
  · exact ⟨fun _ => emptyPartition V, fun _ _ _ hx => hx,
      fun v => isEmptyElim v, fun v => isEmptyElim v⟩
  · obtain ⟨e, he⟩ := exists_surjective_nat V
    let q : ℕ → V := fun n => e (Nat.unpair n).1
    have hfair : ∀ v N, ∃ n, N ≤ n ∧ q n = v := fun v N =>
      let ⟨k, hk⟩ := he v
      ⟨Nat.pair k N, Nat.right_le_pair k N,
        by simpa only [q, Nat.unpair_pair] using hk⟩
    choose R hR using fun (s : {f : V → Option Bool // Persistent G f}) (x : V) =>
      persistent_response G s.property x
    let s : ℕ → {f : V → Option Bool // Persistent G f} :=
      Nat.rec ⟨emptyPartition V, h⟩
        (fun n state => ⟨R state (q n), (hR state (q n)).2⟩)
    have hlegal : ∀ n, IsLegalResponse G (s n).val (s (n + 1)).val (q n) :=
      fun n => (hR (s n) (q n)).1
    have hUF : ∀ v N, ∃ n, N ≤ n ∧ UnfriendlyAt G (s n).val v := fun v N =>
      let ⟨n, hn, hq⟩ := hfair v N
      ⟨n + 1, hn.trans (Nat.le_succ n), hq ▸ (hlegal n).2.2⟩
    have hcover : ∀ v, ∃ n b, (s n).val v = some b := fun v =>
      let ⟨n, _, b, hb, _⟩ := hUF v 0
      ⟨n, b, hb⟩
    exact ⟨fun n => (s n).val, fun n => (hlegal n).1, hcover, hUF⟩

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyChain.lean. -/
/-!
# Finite approximation data from an increasing fair play

An increasing sequence that colors every vertex and makes each vertex unfriendly
at arbitrarily late stages determines a total coloring with compatible unfriendly
approximations for every finite set of same-colored neighbors.
-/


namespace TenChallenges.Continuation

variable {V : Type u} (G : SimpleGraph V)

/-- Fair increasing play supplies finite approximation witnesses for its total coloring. -/
theorem chain_data (f : ℕ → (V → Option Bool))
    (hext : ∀ n, Extends (f n) (f (n + 1)))
    (hcover : ∀ v, ∃ n b, f n v = some b)
    (huf : ∀ v N, ∃ n, N ≤ n ∧ UnfriendlyAt G (f n) v) :
    ∃ p : V → Option Bool, ∀ v, ∃ b, p v = some b ∧
      ∀ s : Finset V, (∀ x ∈ s, G.Adj v x ∧ p x = some b) →
        ∃ g, Extends g p ∧ UnfriendlyAt G g v ∧ ∀ x ∈ s, g x = some b := by
  classical
  have hmono : ∀ {m n}, m ≤ n → Extends (f m) (f n) := fun {m n} hmn =>
    Nat.le_induction (P := fun n _ => Extends (f m) (f n))
      (fun _ _ hx => hx) (fun n _ ih x b hx => hext n x b (ih x b hx)) n hmn
  choose index color hcolor using hcover
  let p : V → Option Bool := fun v => some (color v)
  have hFp : ∀ n, Extends (f n) p := fun n v b hv =>
    (hmono (Nat.le_max_right n (index v)) v (color v) (hcolor v)).symm.trans
      (hmono (Nat.le_max_left n (index v)) v b hv)
  refine ⟨p, fun v => ⟨color v, rfl, ?_⟩⟩
  intro s hs
  obtain ⟨n, hn, hu⟩ := huf v (s.sup index)
  exact ⟨f n, hFp n, hu, fun x hx =>
    (hmono ((Finset.le_sup hx).trans hn) x (color x) (hcolor x)).trans (hs x hx).2⟩

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyEquivalence.lean. -/
/-!
# Global unfriendly partitions and all ordinal game clocks

For a countable graph, existence of a global unfriendly partition is equivalent
to winning the game at every ordinal clock in the vertex universe. A global
partition also gives winning strategies for clocks in any independent universe.

This equivalence does not prove either existence statement for all countable
graphs. In particular, it does not prove that the empty state is persistent.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

variable {V : Type u} (G : SimpleGraph V)

/-- The all-clock game and the global unfriendly-partition assertion are equivalent. -/
theorem unfriendly_partition_iff_persistent [Countable V] :
    (∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) ↔
      Persistent G (emptyPartition V) := by
  exact ⟨fun ⟨p, hp⟩ α => partitionerWins_of_unfriendly_partition G p hp α,
    fun h =>
      let ⟨f, hext, hcover, huf⟩ := persistent_fair_play G h
      let ⟨p, hp⟩ := chain_data G f hext hcover huf
      ⟨p, fun x => let ⟨b, hpx, ha⟩ := hp x
        unfriendlyAt_of_finite_approximations G p x b hpx ha⟩⟩

/-- The equivalence with the clock quantifier written explicitly. -/
theorem unfriendly_partition_iff_all_clocks [Countable V] :
    (∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) ↔
      ∀ α : Ordinal.{u}, PartitionerWins G (emptyPartition V) α :=
  unfriendly_partition_iff_persistent G

/-- A global partition supplies all clocks in an independent universe, without countability. -/
theorem all_clocks_of_global
    (h : ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  fun α => let ⟨p, hp⟩ := h
    partitionerWins_of_unfriendly_partition G p hp α

/-- All clocks in the vertex universe imply all clocks in any other universe. -/
theorem all_clocks_transfer_universe [Countable V]
    (h : ∀ α : Ordinal.{u}, PartitionerWins G (emptyPartition V) α) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G ((unfriendly_partition_iff_all_clocks G).mpr h)

end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyBatchRepair.lean. -/
/-!
# Finite repair after a batch change

A change on arbitrarily many vertices can be repaired in a strongly maximal
domain when it destroys only finitely many crossing edges.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators symmDiff

variable {V : Type u}

/-- Directed crossing edges destroyed by changing colours from `c` to `d`. -/
def lostCrossings (G : SimpleGraph V) (c d : V → Bool) : Set (V × V) :=
  {e | G.Adj e.1 e.2 ∧ c e.1 ≠ c e.2 ∧ d e.1 = d e.2}

open Classical in
private theorem edgeDelta_le_with_lost_crossing (G : SimpleGraph V) (c d : V → Bool)
    (S : Finset V) (e : V × V) :
    edgeDelta G d (flip d S) e ≤ edgeDelta G c (flip c S) e +
      (if e ∈ lostCrossings G c d then 2 else 0) := by
  obtain ⟨x, y⟩ := e
  by_cases ha : G.Adj x y <;> by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
    by_cases hc : c x = c y <;> by_cases hd : d x = d y <;>
    simp_all [edgeDelta, cutIndicator, flip, lostCrossings, Bool.eq_not_iff]

private theorem gain_le_of_finite_loss (G : SimpleGraph V) (c d : V → Bool)
    (S : Finset V) (hS : ∀ x ∈ S, (G.neighborSet x).Finite)
    (hR : (lostCrossings G c d).Finite) :
    gain G d S ≤ gain G c S + 2 * (hR.toFinset.card : ℤ) := by
  classical
  let U := (incident_finite G S hS).toFinset ∪ hR.toFinset
  have hsum (q : V → Bool) : gain G q S = ∑ e ∈ U, edgeDelta G q (flip q S) e :=
    finsum_eq_sum_of_support_subset _ (fun e he => Finset.mem_union_left _
      ((incident_finite G S hS).mem_toFinset.mpr (support_edgeDelta_flip_subset G q S he)))
  have hle := Finset.sum_le_sum (s := U)
    (fun e (_ : e ∈ U) => edgeDelta_le_with_lost_crossing G c d S e)
  have hbonus : (∑ e ∈ U, if e ∈ lostCrossings G c d then (2 : ℤ) else 0) =
      2 * (hR.toFinset.card : ℤ) := by
    have hfilter : U.filter (fun e => e ∈ lostCrossings G c d) = hR.toFinset :=
      Finset.ext fun e => Finset.mem_filter.trans
        ⟨fun h => hR.mem_toFinset.mpr h.2, fun h =>
          ⟨Finset.mem_union_right _ h, hR.mem_toFinset.mp h⟩⟩
    simp [Finset.sum_ite, hfilter, mul_comm]
  simpa only [Finset.sum_add_distrib, ← hsum d, ← hsum c, hbonus] using hle

/-- A change destroying finitely many crossing edges admits a finite repair
in any strongly maximal domain. -/
theorem exists_strongMaximal_of_finite_lostCrossings (G : SimpleGraph V) (A : Set V)
    (c d : V → Bool) (hc : StrongMaximal G A c) (hR : (lostCrossings G c d).Finite) :
    ∃ S : Finset V, (S : Set V) ⊆ A ∧
      (∀ x ∈ S, (G.neighborSet x).Finite) ∧ StrongMaximal G A (flip d S) := by
  classical
  let allowed : Finset V → Prop := fun S =>
    (S : Set V) ⊆ A ∧ ∀ x ∈ S, (G.neighborSet x).Finite
  have hempty : allowed ∅ := by simp [allowed]
  have hclosed (S T : Finset V) (hS : allowed S) (hT : allowed T) : allowed (S ∆ T) :=
    ⟨fun x hx => (Finset.mem_symmDiff.mp hx).elim
      (fun h => hS.1 h.1) (fun h => hT.1 h.1),
    fun x hx => (Finset.mem_symmDiff.mp hx).elim
      (fun h => hS.2 x h.1) (fun h => hT.2 x h.1)⟩
  have hbound (S : Finset V) (hS : allowed S) :
      gain G d S ≤ 2 * (hR.toFinset.card : ℤ) :=
    (gain_le_of_finite_loss G c d S hS.2 hR).trans
      ((Int.add_le_add_right (hc S hS.1 hS.2) _).trans_eq (zero_add _))
  obtain ⟨S, hS, hstable⟩ := FiniteRepair.exists_stable_flip allowed hempty hclosed
    flip (gain G) (fun q S T hS hT => gain_symmDiff G q S T hS.2 hT.2)
    d (2 * (hR.toFinset.card : ℤ)) hbound
  exact ⟨S, hS.1, hS.2, fun T hTA hTN => hstable T ⟨hTA, hTN⟩⟩

open Classical in
/-- Reverse the colours on a set, which can be infinite. -/
noncomputable def flipSet (c : V → Bool) (B : Set V) : V → Bool :=
  fun x => if x ∈ B then !(c x) else c x

/-- Directed opposite-colour edges pointing out of the batch. -/
def batchOppositeEdges (G : SimpleGraph V) (c : V → Bool) (B : Set V) : Set (V × V) :=
  {e | e.1 ∈ B ∧ e.2 ∉ B ∧ G.Adj e.1 e.2 ∧ c e.1 ≠ c e.2}

/-- Serve an arbitrary batch of hubs with infinite degree outside the batch.
The original opposite-colour edges leaving the batch must be finite, and all
other hubs must already have infinite opposite neighbourhoods. -/
theorem exists_unfriendly_of_finite_batch_budget [Countable V] (G : SimpleGraph V)
    (c : V → Bool) (B : Set V)
    (hc : StrongMaximal G {x | (G.neighborSet x).Finite} c)
    (hB : ∀ x ∈ B, (G.neighborSet x \ B).Infinite)
    (hbudget : (batchOppositeEdges G c B).Finite)
    (hout : ∀ x ∉ B, (G.neighborSet x).Infinite → (oppositeSet G c x).Infinite) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  classical
  let d := flipSet c B
  have hR : (lostCrossings G c d).Finite := (hbudget.union (hbudget.image Prod.swap)).subset (by
    rintro ⟨x, y⟩ h
    by_cases hx : x ∈ B
    · exact Or.inl ⟨hx, fun hy => h.2.1 (by simpa [d, flipSet, hx, hy] using h.2.2), h.1, h.2.1⟩
    have hy : y ∈ B :=
      Classical.byContradiction fun hy => h.2.1 (by simpa [d, flipSet, hx, hy] using h.2.2)
    exact Or.inr ⟨(y, x), ⟨hy, hx, h.1.symm, Ne.symm h.2.1⟩, rfl⟩)
  have hop (x : V) (hNx : (G.neighborSet x).Infinite) : (oppositeSet G d x).Infinite := by
    by_cases hx : x ∈ B
    · refine ((hB x hx).sdiff (hbudget.image Prod.snd)).mono ?_
      intro y hy
      have heq : c y = c x := Classical.byContradiction fun hne =>
        hy.2 ⟨(x, y), ⟨hx, hy.1.2, hy.1.1, Ne.symm hne⟩, rfl⟩
      exact ⟨hy.1.1, by simp [d, flipSet, hx, hy.1.2, heq]⟩
    · refine ((hout x hx hNx).sdiff (hbudget.image Prod.fst)).mono ?_
      intro y hy
      have hyB : y ∉ B := fun hyB =>
        hy.2 ⟨(y, x), ⟨hyB, hx, hy.1.1.symm, hy.1.2⟩, rfl⟩
      exact ⟨hy.1.1, by simpa [d, flipSet, hx, hyB] using hy.1.2⟩
  obtain ⟨S, _, hS, hmax⟩ := exists_strongMaximal_of_finite_lostCrossings G _ c d hc hR
  refine ⟨fun x => some (flip d S x), fun x =>
    (Classical.em (G.neighborSet x).Finite).elim
      (fun hx => unfriendlyAt_of_strongMaximal G _ _ hmax x hx hx)
      (fun hx => unfriendly_of_infinite_opposite G _ x
        (infinite_opposite_flip G d x S (fun hxS => hx (hS x hxS))
          (hop x (Set.not_finite.mp hx))))⟩

/-- The finite batch budget condition reaches every ordinal clock. -/
theorem all_clocks_of_finite_batch_budget [Countable V] (G : SimpleGraph V)
    (c : V → Bool) (B : Set V)
    (hc : StrongMaximal G {x | (G.neighborSet x).Finite} c)
    (hB : ∀ x ∈ B, (G.neighborSet x \ B).Infinite)
    (hbudget : (batchOppositeEdges G c B).Finite)
    (hout : ∀ x ∉ B, (G.neighborSet x).Infinite → (oppositeSet G c x).Infinite) :
    ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r :=
  all_clocks_of_global G (exists_unfriendly_of_finite_batch_budget G c B hc hB hbudget hout)

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyBatchImbalance.lean. -/
/-!
# Signed imbalance after a batch of hub flips

For a finite flip outside the batch, a lost crossing edge contributes four
to the gain difference at its flipped endpoint. A newly crossing edge
contributes negative four. Only their net imbalance at each vertex matters.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators symmDiff

variable {V : Type u}

open Classical in
/-- The excess of opposite-coloured neighbours over same-coloured neighbours
inside the batch. At a finite-degree vertex this is a finite sum. -/
noncomputable def batchImbalance (G : SimpleGraph V) (c : V → Bool) (B : Set V) (x : V) : ℤ :=
  ∑ᶠ y, if y ∈ G.neighborSet x ∩ B then (if c y = c x then -1 else 1) else 0

open Classical in
private theorem batchImbalance_eq_sum (G : SimpleGraph V) (c : V → Bool) (B : Set V) (x : V)
    (hN : (G.neighborSet x).Finite) :
    batchImbalance G c B x =
      ∑ y ∈ hN.toFinset, if y ∈ B then (if c y = c x then -1 else 1) else 0 := by
  unfold batchImbalance
  refine (finsum_eq_sum_of_support_subset (s := hN.toFinset) _ ?_).trans ?_
  · intro y hy
    exact hN.mem_toFinset.mpr (Classical.byContradiction fun hn =>
      hy (if_neg (fun hb => hn hb.1)))
  exact Finset.sum_congr rfl fun y hy => by
    simp only [Set.mem_inter_iff, hN.mem_toFinset.mp hy, true_and]

open Classical in
private theorem gain_singleton_eq_sum (G : SimpleGraph V) (c : V → Bool) (x : V)
    (hN : (G.neighborSet x).Finite) :
    gain G c {x} = 2 * ∑ y ∈ hN.toFinset, (if c y = c x then 1 else -1) := by
  rw [gain_singleton G c x hN, Finset.sum_ite]
  simp [sub_eq_add_neg]

private theorem singleton_flip_arith (a b : Bool) :
    2 * (if (!b) = a then (1 : ℤ) else -1) =
      2 * (if b = a then 1 else -1) + 4 * (if b = a then -1 else 1) := by
  cases a <;> cases b <;> decide

private theorem gain_flipSet_singleton_eq_add_batchImbalance (G : SimpleGraph V)
    (c : V → Bool) (B : Set V) (x : V) (hx : x ∉ B) (hN : (G.neighborSet x).Finite) :
    gain G (flipSet c B) {x} = gain G c {x} + 4 * batchImbalance G c B x := by
  classical
  simp only [gain_singleton_eq_sum G (flipSet c B) x hN, gain_singleton_eq_sum G c x hN,
    batchImbalance_eq_sum G c B x hN, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ B
  · simpa only [flipSet, if_neg hx, if_pos hy] using singleton_flip_arith (c x) (c y)
  · simp [flipSet, hx, hy]

private theorem flip_flipSet_comm (c : V → Bool) (B : Set V) (S : Finset V) :
    flip (flipSet c B) S = flipSet (flip c S) B := by
  funext x
  by_cases hs : x ∈ S <;> by_cases hb : x ∈ B <;> simp [flip, flipSet, hs, hb]

private theorem batchImbalance_flip_eq (G : SimpleGraph V) (c : V → Bool) (B : Set V)
    (S : Finset V) (hSB : ∀ y ∈ S, y ∉ B) (x : V) (hx : x ∉ S) :
    batchImbalance G (flip c S) B x = batchImbalance G c B x := by
  unfold batchImbalance
  apply finsum_congr
  intro y
  by_cases hy : y ∈ G.neighborSet x ∩ B
  · simp [hy, flip, hx, show y ∉ S from fun hs => hSB y hs hy.2]
  · simp [hy]

/-- For a finite flip outside the batch, the difference of its directed gains
is four times the sum of the batch imbalances at the flipped vertices. -/
theorem gain_flipSet_eq_add_batchImbalance (G : SimpleGraph V) (c : V → Bool)
    (B : Set V) (S : Finset V) (hSf : ∀ x ∈ S, (G.neighborSet x).Finite)
    (hSB : ∀ x ∈ S, x ∉ B) :
    gain G (flipSet c B) S = gain G c S + 4 * ∑ x ∈ S, batchImbalance G c B x := by
  classical
  induction S using Finset.induction_on
  case empty => simp
  case insert x S hx ih =>
    have hSf' : ∀ y ∈ S, (G.neighborSet y).Finite := fun y hy => hSf y (Finset.mem_insert_of_mem hy)
    have hSB' : ∀ y ∈ S, y ∉ B := fun y hy => hSB y (Finset.mem_insert_of_mem hy)
    have hxB : x ∉ B := hSB x (Finset.mem_insert_self _ _)
    have hxN : (G.neighborSet x).Finite := hSf x (Finset.mem_insert_self _ _)
    have hsx : ∀ y ∈ ({x} : Finset V), (G.neighborSet y).Finite :=
      fun y hy => (Finset.mem_singleton.mp hy).symm ▸ hxN
    have hsplit : S ∆ ({x} : Finset V) = insert x S :=
      (Finset.symmDiff_eq_union (Finset.disjoint_singleton_right.mpr hx)).trans
        (by rw [Finset.union_comm, Finset.singleton_union])
    have split (q : V → Bool) : gain G q (insert x S) =
        gain G q S + gain G (flip q S) {x} :=
      hsplit ▸ gain_symmDiff G q S {x} hSf' hsx
    rw [split (flipSet c B), split c, flip_flipSet_comm,
      gain_flipSet_singleton_eq_add_batchImbalance G (flip c S) B x hxB hxN,
      batchImbalance_flip_eq G c B S hSB' x hx, ih hSf' hSB', Finset.sum_insert hx]
    omega

private theorem exists_strongMaximal_of_bounded_gain (G : SimpleGraph V) (A : Set V)
    (d : V → Bool) (K : ℤ) (h : ∀ S : Finset V, (S : Set V) ⊆ A →
      (∀ x ∈ S, (G.neighborSet x).Finite) → gain G d S ≤ K) :
    ∃ S : Finset V, (S : Set V) ⊆ A ∧ (∀ x ∈ S, (G.neighborSet x).Finite) ∧
      StrongMaximal G A (flip d S) := by
  classical
  let allowed (S : Finset V) : Prop := (S : Set V) ⊆ A ∧ ∀ x ∈ S, (G.neighborSet x).Finite
  have hclosed (S T : Finset V) (hS : allowed S) (hT : allowed T) : allowed (S ∆ T) := by
    have mem (x : V) (hx : x ∈ S ∆ T) : x ∈ S ∨ x ∈ T :=
      (Finset.mem_symmDiff.mp hx).imp And.left And.left
    exact ⟨fun x hx => (mem x hx).elim (fun hs => hS.1 hs) (fun ht => hT.1 ht),
      fun x hx => (mem x hx).elim (hS.2 x) (hT.2 x)⟩
  obtain ⟨S, hS, hmax⟩ := FiniteRepair.exists_stable_flip allowed (by simp [allowed]) hclosed
    flip (gain G) (fun q S T hS hT => gain_symmDiff G q S T hS.2 hT.2)
    d K (fun S hS => h S hS.1 hS.2)
  exact ⟨S, hS.1, hS.2, fun T hTA hTf => hmax T ⟨hTA, hTf⟩⟩

private theorem sum_batchImbalance_le (G : SimpleGraph V) (c : V → Bool) (B : Set V)
    (hpos : {x | (G.neighborSet x).Finite ∧ 0 < batchImbalance G c B x}.Finite)
    (S : Finset V) (hSf : ∀ x ∈ S, (G.neighborSet x).Finite) :
    (∑ x ∈ S, batchImbalance G c B x) ≤
      ∑ x ∈ hpos.toFinset, batchImbalance G c B x := by
  classical
  let b := batchImbalance G c B
  let P := S.filter fun x => 0 < b x
  have hsum := Finset.sum_filter_add_sum_filter_not S (fun x => 0 < b x) b
  have hn : (∑ x ∈ S.filter (fun x => ¬ (0 < b x)), b x) ≤ 0 :=
    Finset.sum_nonpos fun _ hx => le_of_not_gt (Finset.mem_filter.mp hx).2
  have hsub : P ⊆ hpos.toFinset := fun x hx =>
    let ⟨hxS, hxP⟩ := Finset.mem_filter.mp hx
    hpos.mem_toFinset.mpr ⟨hSf x hxS, hxP⟩
  exact (hsum.symm.trans_le (add_le_of_nonpos_right hn)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ hx _ => (hpos.mem_toFinset.mp hx).2.le)

/-- With independent hubs, flip the bad batch and repair finitely many
finite-degree vertices whenever positive batch imbalances occur only finitely often. -/
theorem exists_strong_unfriendly_of_finite_batch_imbalance (G : SimpleGraph V)
    (c : V → Bool) (B : Set V)
    (hc : StrongMaximal G {x | (G.neighborSet x).Finite} c)
    (hindep : ∀ x y, (G.neighborSet x).Infinite → (G.neighborSet y).Infinite → ¬ G.Adj x y)
    (hbad : ∀ x ∈ B, (G.neighborSet x).Infinite ∧ (oppositeSet G c x).Finite)
    (hout : ∀ x ∉ B, (G.neighborSet x).Infinite → (oppositeSet G c x).Infinite)
    (hpos : {x | (G.neighborSet x).Finite ∧ 0 < batchImbalance G c B x}.Finite) :
    ∃ q : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} q ∧
      ∀ x, (G.neighborSet x).Infinite → (oppositeSet G q x).Infinite := by
  classical
  let d := flipSet c B
  let K := 4 * ∑ x ∈ hpos.toFinset, batchImbalance G c B x
  have hbound (S : Finset V) (hS : (S : Set V) ⊆ {x | (G.neighborSet x).Finite})
      (hSf : ∀ x ∈ S, (G.neighborSet x).Finite) : gain G d S ≤ K := by
    have hSB : ∀ x ∈ S, x ∉ B := fun x hx hxb => (hbad x hxb).1 (hSf x hx)
    change gain G (flipSet c B) S ≤ K
    rw [gain_flipSet_eq_add_batchImbalance G c B S hSf hSB]
    have hle := sum_batchImbalance_le G c B hpos S hSf
    have hg := hc S hS hSf
    dsimp only [K]
    omega
  obtain ⟨S, _, hSf, hmax⟩ := exists_strongMaximal_of_bounded_gain G _ d K hbound
  refine ⟨flip d S, hmax, ?_⟩
  intro x hx
  apply infinite_opposite_flip G d x S (fun h => hx (hSf x h))
  have houtside (y : V) (ha : G.Adj x y) : y ∉ B :=
    fun hy => hindep x y hx (hbad y hy).1 ha
  by_cases hxb : x ∈ B
  · refine (hx.sdiff (hbad x hxb).2).mono fun y hy => ?_
    have heq : c y = c x := Classical.byContradiction fun hn => hy.2 ⟨hy.1, hn⟩
    exact ⟨hy.1, by simp [d, flipSet, hxb, houtside y hy.1, heq]⟩
  · exact (hout x hxb hx).mono fun y hy =>
      ⟨hy.1, by simpa [d, flipSet, hxb, houtside y hy.1] using hy.2⟩

/-- Finite positive imbalance also suffices for every ordinal clock. -/
theorem all_clocks_of_finite_batch_imbalance [Countable V] (G : SimpleGraph V)
    (c : V → Bool) (B : Set V)
    (hc : StrongMaximal G {x | (G.neighborSet x).Finite} c)
    (hindep : ∀ x y, (G.neighborSet x).Infinite → (G.neighborSet y).Infinite → ¬ G.Adj x y)
    (hbad : ∀ x ∈ B, (G.neighborSet x).Infinite ∧ (oppositeSet G c x).Finite)
    (hout : ∀ x ∉ B, (G.neighborSet x).Infinite → (oppositeSet G c x).Infinite)
    (hpos : {x | (G.neighborSet x).Finite ∧ 0 < batchImbalance G c B x}.Finite) :
    ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r := by
  obtain ⟨q, hmax, hq⟩ := exists_strong_unfriendly_of_finite_batch_imbalance
    G c B hc hindep hbad hout hpos
  apply all_clocks_of_global G
  refine ⟨fun x => some (q x), ?_⟩
  intro x
  exact (G.neighborSet x).finite_or_infinite.elim
    (fun hx => unfriendlyAt_of_strongMaximal G _ q hmax x hx hx)
    (fun hx => unfriendly_of_infinite_opposite G q x (hq x hx))

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyBoundedLoss.lean. -/
/-!
# Limits of finite flips with bounded cut loss

A finite-coordinate test records how many members of a protected neighbour
set have reverted to a given colour. Its bound transfers through the
product closure of finite flips with a common lower bound on their gains.
All gains use the directed-edge convention of `Energy.gain`.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.BoundedLoss

open Energy
open scoped symmDiff

variable {V : Type u} (G : SimpleGraph V) (B : Set V)

/-- Colourings reachable by one finite flip with directed loss at most `D`. -/
def orbit (c : V → Bool) (D : ℤ) : Set (V → Bool) :=
  {p | ∃ S : Finset V, (S : Set V) ⊆ B ∧ -D ≤ gain G c S ∧ p = flip c S}

/-- Finite witness tests avoid extended-natural-valued counts. -/
def Controls (c : V → Bool) (Q : Set V) (b : Bool) (C : ℤ) : Prop :=
  ∀ (S : Finset V), (S : Set V) ⊆ B → ∀ (U : Finset V), (U : Set V) ⊆ Q →
    (∀ x ∈ U, flip c S x = b) → 4 * (U.card : ℤ) + gain G c S ≤ C

private theorem match_finset_of_mem_closure [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set (V → Bool)} {d : V → Bool} (hd : d ∈ closure A) (W : Finset V) :
    ∃ p ∈ A, ∀ x ∈ W, p x = d x := by
  let cylinder := ⋂ x ∈ W, {p : V → Bool | p x = d x}
  have hopen : IsOpen cylinder := isOpen_biInter_finset fun x _ =>
    (isOpen_discrete ({d x} : Set Bool)).preimage
      (show Continuous (fun p : V → Bool => p x) from continuous_apply x)
  obtain ⟨p, hp, ha⟩ := mem_closure_iff.mp hd cylinder hopen
    (Set.mem_iInter₂.mpr fun _ _ => rfl)
  exact ⟨p, ha, Set.mem_iInter₂.mp hp⟩

private theorem symmDiff_allowed {S T : Finset V} [DecidableEq V]
    (hS : (S : Set V) ⊆ B) (hT : (T : Set V) ⊆ B) : (↑(S ∆ T) : Set V) ⊆ B :=
  fun _ hx => (Finset.mem_symmDiff.mp hx).elim (fun h => hS h.1) (fun h => hT h.1)

private theorem exists_comparison [TopologicalSpace Bool] [DiscreteTopology Bool]
    {c d : V → Bool} {D : ℤ} (hd : d ∈ closure (orbit G B c D))
    (F U : Finset V) (hF : ∀ x ∈ F, (G.neighborSet x).Finite) :
    ∃ T : Finset V, (T : Set V) ⊆ B ∧ -D ≤ gain G c T ∧
      (∀ x ∈ U, flip c T x = d x) ∧ gain G (flip c T) F = gain G d F := by
  classical
  obtain ⟨W, hW⟩ := gain_finite_dependence G F hF
  obtain ⟨_, ⟨T, hTB, hgain, rfl⟩, h⟩ := match_finset_of_mem_closure hd (U ∪ W)
  exact ⟨T, hTB, hgain, fun x hx => h x (Finset.mem_union_left _ hx),
    hW _ _ fun x hx => h x (Finset.mem_union_right _ hx)⟩

/-- A bounded-loss limit has gain at most the loss allowance on every finite flip. -/
theorem gain_le_of_mem_closure [TopologicalSpace Bool] [DiscreteTopology Bool]
    {c d : V → Bool} {D : ℤ} (hd : d ∈ closure (orbit G B c D))
    (hB : ∀ x ∈ B, (G.neighborSet x).Finite) (hc : StrongMaximal G B c)
    (F : Finset V) (hF : (F : Set V) ⊆ B) : gain G d F ≤ D := by
  classical
  obtain ⟨T, hT, hloss, _, hgain⟩ := exists_comparison G B hd F ∅ (fun x hx => hB x (hF hx))
  have hTF := symmDiff_allowed B hT hF
  have hmax := hc (T ∆ F) hTF (fun x hx => hB x (hTF hx))
  have hsum := gain_symmDiff G c T F (fun x hx => hB x (hT hx)) (fun x hx => hB x (hF hx))
  omega

/-- A certificate for reverted neighbours passes through bounded-loss closure
with only the stated additive increase in its allowance. -/
theorem controls_of_mem_closure [TopologicalSpace Bool] [DiscreteTopology Bool]
    {c d : V → Bool} {D C : ℤ} {Q : Set V} {b : Bool}
    (hd : d ∈ closure (orbit G B c D)) (hB : ∀ x ∈ B, (G.neighborSet x).Finite)
    (hc : Controls G B c Q b C) : Controls G B d Q b (C + D) := by
  classical
  intro F hF U hU hmatch
  obtain ⟨T, hT, hloss, hfix, hgain⟩ := exists_comparison G B hd F U (fun x hx => hB x (hF hx))
  have hcol (x : V) (hx : x ∈ U) : flip c (T ∆ F) x = b := by
    rw [flip_symmDiff]
    exact (congrArg (fun a : Bool => if x ∈ F then !a else a) (hfix x hx)).trans (hmatch x hx)
  have htest := hc (T ∆ F) (symmDiff_allowed B hT hF) U hU hcol
  have hsum := gain_symmDiff G c T F (fun x hx => hB x (hT hx)) (fun x hx => hB x (hF hx))
  omega

/-- Finite flips and their closure fix every boundary bit. -/
theorem eqOn_compl_of_mem_closure [TopologicalSpace Bool] [DiscreteTopology Bool]
    {c d : V → Bool} {D : ℤ} (hd : d ∈ closure (orbit G B c D)) : Set.EqOn d c Bᶜ := by
  classical
  intro x hx
  obtain ⟨_, ⟨T, hT, _, rfl⟩, heq⟩ := match_finset_of_mem_closure hd {x}
  exact (heq x (Finset.mem_singleton_self _)).symm.trans (if_neg (fun h => hx (hT h)))

/-- Only finitely many recorded neighbours can have reverted at a controlled colouring. -/
theorem finite_reversions {c : V → Bool} {Q : Set V} {b : Bool} {C : ℤ}
    (hc : Controls G B c Q b C) : {x | x ∈ Q ∧ c x = b}.Finite := by
  classical
  by_contra hi
  obtain ⟨U, hU, hcard⟩ := (show {x | x ∈ Q ∧ c x = b}.Infinite from hi).exists_subset_card_eq
    (C.toNat + 1)
  have h := hc ∅ (by simp) U (fun _ hx => (hU hx).1) (fun x hx => by
    simpa using (hU hx).2)
  rw [gain_empty, add_zero, hcard] at h
  omega

/-- A recorded infinite neighbour set continues to supply the hub at every bounded loss. -/
theorem infinite_opponents_of_mem_closure [TopologicalSpace Bool] [DiscreteTopology Bool]
    {c d : V → Bool} {Q : Set V} {C D : ℤ} {h : V} (hout : h ∉ B)
    (hB : ∀ x ∈ B, (G.neighborSet x).Finite) (hd : d ∈ closure (orbit G B c D))
    (hc : Controls G B c Q (c h) C) (hQ : Q.Infinite) (hN : Q ⊆ G.neighborSet h ∩ B) :
    (oppositeSet G d h ∩ B).Infinite := by
  have heq := eqOn_compl_of_mem_closure G B hd hout
  have hfin := finite_reversions G B (controls_of_mem_closure G B hd hB hc)
  exact (hQ.sdiff hfin).mono fun x hx => ⟨⟨(hN hx.1).1,
    fun e => hx.2 ⟨hx.1, e.trans heq⟩⟩, (hN hx.1).2⟩

/-- Recentring at a nonnegative-gain finite flip preserves the stored loss allowance. -/
theorem controls_after_flip {c : V → Bool} {Q : Set V} {b : Bool} {C : ℤ} {T : Finset V}
    (hc : Controls G B c Q b C) (hB : ∀ x ∈ B, (G.neighborSet x).Finite)
    (hT : (T : Set V) ⊆ B) (hn : 0 ≤ gain G c T) : Controls G B (flip c T) Q b C := by
  classical
  intro F hF U hU hmatch
  have h := hc (T ∆ F) (symmDiff_allowed B hT hF) U hU (by rwa [flip_symmDiff])
  rw [gain_symmDiff G c T F (fun x hx => hB x (hT hx)) (fun x hx => hB x (hF hx))] at h
  omega

/-- The old neighbours that become opponents when a hub reverses its colour. -/
def matchingSet (c : V → Bool) (h : V) : Set V := {x | G.Adj h x ∧ c x = c h}

open Classical in
private theorem singleton_imbalance (c : V → Bool) (h x : V) :
    batchImbalance G c {h} x = (if x ∈ oppositeSet G c h then 1 else 0) -
      (if x ∈ matchingSet G c h then 1 else 0) := by
  unfold batchImbalance
  rw [finsum_eq_single _ h (fun y hy => by simp [hy])]
  by_cases ha : G.Adj h x <;> by_cases he : c x = c h <;>
    simp [oppositeSet, matchingSet, ha, G.adj_comm x h, he, eq_comm (a := c h)]

open Classical in
/-- Exact directed gain after changing a boundary vertex, without any
finiteness condition on the full neighbourhood of that vertex. -/
theorem gain_boundary_flip (c : V → Bool) (h : V) (F : Finset V) (hout : h ∉ F)
    (hF : ∀ x ∈ F, (G.neighborSet x).Finite) :
    gain G (flip c {h}) F = gain G c F + 4 * (((F.filter (· ∈ oppositeSet G c h)).card : ℤ) -
      ((F.filter (· ∈ matchingSet G c h)).card : ℤ)) := by
  have heq : flip c {h} = flipSet c {h} := funext fun x => by simp [Energy.flip, flipSet]
  rw [heq, gain_flipSet_eq_add_batchImbalance G c {h} F hF
    (fun x hx he => hout ((Set.mem_singleton_iff.mp he) ▸ hx))]
  simp [singleton_imbalance, Finset.sum_sub_distrib]

/-- A recorded hub has an infinite neighbour set with a finite loss allowance. -/
def Recorded (c : V → Bool) (h : V) : Prop :=
  ∃ Q : Set V, Q ⊆ G.neighborSet h ∩ B ∧ Q.Infinite ∧ ∃ C : ℤ, Controls G B c Q (c h) C

private theorem recorded_of_mem_closure [TopologicalSpace Bool] [DiscreteTopology Bool]
    {c d : V → Bool} {D : ℤ} (hd : d ∈ closure (orbit G B c D))
    (hB : ∀ x ∈ B, (G.neighborSet x).Finite) {h : V} (hout : h ∉ B)
    (hc : Recorded G B c h) : Recorded G B d h := by
  obtain ⟨Q, hN, hi, C, hctl⟩ := hc
  exact ⟨Q, hN, hi, C + D, (eqOn_compl_of_mem_closure G B hd hout).symm ▸
    controls_of_mem_closure G B hd hB hctl⟩

open Classical in
private theorem charge_boundary_flip (d : V → Bool) (h : V) (hout : h ∉ B)
    (hB : ∀ x ∈ B, (G.neighborSet x).Finite) (ho : (oppositeSet G d h ∩ B).Finite)
    (F : Finset V) (hF : (F : Set V) ⊆ B) (U : Finset V)
    (hU : U ⊆ F.filter (· ∈ matchingSet G d h)) :
    4 * (U.card : ℤ) + gain G (flip d {h}) F ≤ gain G d F + 4 * (ho.toFinset.card : ℤ) := by
  rw [gain_boundary_flip G d h F (fun hf => hout (hF hf)) (fun x hx => hB x (hF hx))]
  have hs : F.filter (· ∈ oppositeSet G d h) ⊆ ho.toFinset := fun x hx =>
    ho.mem_toFinset.mpr ⟨(Finset.mem_filter.mp hx).2, hF (Finset.mem_filter.mp hx).1⟩
  have hl := Finset.card_le_card hs
  have hu := Finset.card_le_card hU
  omega

private theorem gain_after_boundary_flip_le (d : V → Bool) (h : V) (hout : h ∉ B)
    (hB : ∀ x ∈ B, (G.neighborSet x).Finite) (ho : (oppositeSet G d h ∩ B).Finite)
    (F : Finset V) (hF : (F : Set V) ⊆ B) :
    gain G (flip d {h}) F ≤ gain G d F + 4 * (ho.toFinset.card : ℤ) := by
  classical
  simpa using charge_boundary_flip G B d h hout hB ho F hF ∅ (Finset.empty_subset _)

/-- Reversing a hub with finitely many opponents creates a loss certificate
for its infinite set of formerly matching neighbours. -/
theorem recorded_after_boundary_flip (d : V → Bool) (h : V) (D : ℤ) (hout : h ∉ B)
    (hB : ∀ x ∈ B, (G.neighborSet x).Finite) (ho : (oppositeSet G d h ∩ B).Finite)
    (hi : (G.neighborSet h ∩ B).Infinite)
    (hgain : ∀ F : Finset V, (F : Set V) ⊆ B → gain G d F ≤ D) :
    Recorded G B (flip d {h}) h := by
  classical
  let Q := (G.neighborSet h ∩ B) \ (oppositeSet G d h ∩ B)
  refine ⟨Q, Set.sdiff_subset, hi.sdiff ho, D + 4 * (ho.toFinset.card : ℤ), ?_⟩
  intro F hF U hU hmatch
  have hm (x : V) (hx : x ∈ U) : x ∈ matchingSet G d h :=
    ⟨(hU hx).1.1, Classical.byContradiction fun hn =>
      (hU hx).2 ⟨⟨(hU hx).1.1, hn⟩, (hU hx).1.2⟩⟩
  have hUF (x : V) (hx : x ∈ U) : x ∈ F := by
    by_contra hn
    have hne : x ≠ h := fun e => hout (e ▸ (hU hx).1.2)
    simpa [Energy.flip, hn, hne, (hm x hx).2] using hmatch x hx
  exact (charge_boundary_flip G B d h hout hB ho F hF U
    (fun x hx => Finset.mem_filter.mpr ⟨hUF x hx, hm x hx⟩)).trans (add_le_add (hgain F hF) le_rfl)

private theorem recorded_other_boundary_flip (d : V → Bool) (h v : V) (hout : h ∉ B)
    (hB : ∀ x ∈ B, (G.neighborSet x).Finite) (ho : (oppositeSet G d h ∩ B).Finite)
    (hne : v ≠ h) (hv : Recorded G B d v) : Recorded G B (flip d {h}) v := by
  classical
  obtain ⟨Q, hN, hi, C, hctl⟩ := hv
  refine ⟨Q, hN, hi, C + 4 * (ho.toFinset.card : ℤ), ?_⟩
  intro F hF U hU hmatch
  have hUcol (x : V) (hx : x ∈ U) : flip d F x = d v := by
    have hxh : x ≠ h := fun e => hout (e ▸ (hN (hU hx)).2)
    simpa [Energy.flip, hxh, hne] using hmatch x hx
  have hprev := hctl F hF U hU hUcol
  have hg := gain_after_boundary_flip_le G B d h hout hB ho F hF
  omega

private theorem exists_maximal_finite_flip (q : V → Bool) (K : ℤ)
    (hB : ∀ x ∈ B, (G.neighborSet x).Finite)
    (hbound : ∀ F : Finset V, (F : Set V) ⊆ B → gain G q F ≤ K) :
    ∃ T : Finset V, (T : Set V) ⊆ B ∧ 0 ≤ gain G q T ∧ StrongMaximal G B (flip q T) := by
  classical
  obtain ⟨m, ⟨T, hT, hval⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ F : Finset V, (F : Set V) ⊆ B ∧ gain G q F = z)
    ⟨K, fun z ⟨F, hF, hz⟩ => hz ▸ hbound F hF⟩
    ⟨0, ∅, by simp, gain_empty G q⟩
  have hpos := hmax 0 ⟨∅, by simp, gain_empty G q⟩
  refine ⟨T, hT, hval.symm ▸ hpos, fun F hF hfin => ?_⟩
  have ht := hmax (gain G q (T ∆ F)) ⟨T ∆ F, symmDiff_allowed B hT hF, rfl⟩
  rw [gain_symmDiff G q T F (fun x hx => hB x (hT hx)) hfin, hval] at ht
  omega

private theorem recorded_after_finite_flip {q : V → Bool} {T : Finset V} {h : V}
    (hout : h ∉ B) (hB : ∀ x ∈ B, (G.neighborSet x).Finite)
    (hT : (T : Set V) ⊆ B) (hn : 0 ≤ gain G q T) (hr : Recorded G B q h) :
    Recorded G B (flip q T) h := by
  obtain ⟨Q, hN, hi, C, hctl⟩ := hr
  exact ⟨Q, hN, hi, C, (show flip q T h = q h from if_neg (fun ht => hout (hT ht))).symm ▸
    controls_after_flip G B hctl hB hT hn⟩

private theorem repair_failed_limit [TopologicalSpace Bool] [DiscreteTopology Bool]
    (hB : ∀ x ∈ B, (G.neighborSet x).Finite) {c d : V → Bool} {D : ℤ} {h : V}
    (hc : StrongMaximal G B c) (hd : d ∈ closure (orbit G B c D))
    (hout : h ∉ B) (hi : (G.neighborSet h ∩ B).Infinite) (ho : (oppositeSet G d h ∩ B).Finite) :
    ∃ p, StrongMaximal G B p ∧ Recorded G B p h ∧
      ∀ v, v ∉ B → v ≠ h → Recorded G B c v → Recorded G B p v := by
  classical
  have hgain := gain_le_of_mem_closure G B hd hB hc
  have hbound (F : Finset V) (hF : (F : Set V) ⊆ B) :
      gain G (flip d {h}) F ≤ D + 4 * (ho.toFinset.card : ℤ) :=
    (gain_after_boundary_flip_le G B d h hout hB ho F hF).trans (add_le_add (hgain F hF) le_rfl)
  obtain ⟨T, hT, hn, hmax⟩ := exists_maximal_finite_flip G B _ _ hB hbound
  refine ⟨flip (flip d {h}) T, hmax, recorded_after_finite_flip G B hout hB hT hn
    (recorded_after_boundary_flip G B d h D hout hB ho hi hgain), ?_⟩
  exact fun v hv hne hr => recorded_after_finite_flip G B hv hB hT hn
    (recorded_other_boundary_flip G B d h v hout hB ho hne
      (recorded_of_mem_closure G B hd hB hv hr))

/-- The hub keeps infinitely many opponents in the movable set at every bounded-loss limit. -/
def Robust [TopologicalSpace Bool] (c : V → Bool) (h : V) : Prop :=
  ∀ (D : ℤ) (d : V → Bool), d ∈ closure (orbit G B c D) → (oppositeSet G d h ∩ B).Infinite

private theorem robust_of_recorded [TopologicalSpace Bool] [DiscreteTopology Bool]
    (hB : ∀ x ∈ B, (G.neighborSet x).Finite) {c : V → Bool} {h : V}
    (hout : h ∉ B) (hc : Recorded G B c h) : Robust G B c h := by
  obtain ⟨Q, hN, hi, C, hctl⟩ := hc
  exact fun _ _ hd => infinite_opponents_of_mem_closure G B hout hB hd hctl hi hN

private theorem finish_hubs [TopologicalSpace Bool] [DiscreteTopology Bool]
    (H : Set V) (hB : ∀ x ∈ B, (G.neighborSet x).Finite)
    (hH : ∀ h ∈ H, h ∉ B ∧ (G.neighborSet h ∩ B).Infinite) (R : Finset V) :
    ∀ c, StrongMaximal G B c → (∀ h ∈ H, h ∉ R → Recorded G B c h) →
      ∃ q, StrongMaximal G B q ∧ ∀ h ∈ H, Robust G B q h := by
  classical
  induction R using Finset.strongInductionOn with | _ R ih => _
  intro c hc hrec
  by_cases hall : ∀ h ∈ H, Robust G B c h
  · exact ⟨c, hc, hall⟩
  obtain ⟨h, hmem, hfail⟩ : ∃ h ∈ H, ¬ Robust G B c h := by simpa using hall
  obtain ⟨D, d, hd, ho⟩ : ∃ D d, d ∈ closure (orbit G B c D) ∧
      (oppositeSet G d h ∩ B).Finite :=
    Classical.byContradiction fun hno => hfail fun D d hd hfin => hno ⟨D, d, hd, hfin⟩
  have hh := hH h hmem
  have hR : h ∈ R := Classical.byContradiction (fun hnot =>
    hfail (robust_of_recorded G B hB hh.1 (hrec h hmem hnot)))
  obtain ⟨p, hp, hnew, hkeep⟩ := repair_failed_limit G B hB hc hd hh.1 hh.2 ho
  refine ih (R.erase h) (Finset.erase_ssubset hR) p hp (fun v hv hVR => ?_)
  by_cases hsame : v = h
  · exact hsame ▸ hnew
  exact hkeep v (hH v hv).1 hsame
    (hrec v hv (fun hvR => hVR (Finset.mem_erase.mpr ⟨hsame, hvR⟩)))

/-- One strongly maximal seed simultaneously serves the finitely many hubs
in every product limit of finite flips of any fixed bounded loss. -/
theorem exists_robust_seed [TopologicalSpace Bool] [DiscreteTopology Bool]
    (H : Set V) (hf : H.Finite) (hB : ∀ x ∈ B, (G.neighborSet x).Finite)
    (hH : ∀ h ∈ H, h ∉ B ∧ (G.neighborSet h ∩ B).Infinite) :
    ∃ c, StrongMaximal G B c ∧ ∀ h ∈ H, Robust G B c h := by
  classical
  obtain ⟨c, _, hc⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G Bᶜ (fun _ => false)
  exact finish_hubs G B H hB hH hf.toFinset c (by simpa using hc)
    (fun h hh hn => (hn (hf.mem_toFinset.mpr hh)).elim)

end TenChallenges.Continuation.BoundedLoss

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

/- Inlined from Continuation/UnfriendlyBoundedLossCells.lean. -/
/-!
# Strongly maximal cuts on cells with finite interfaces

A cell contains its own finite set of hubs and any number of finite-degree
vertices. A finite interface bounds the change in a cell's gain when it is
reinserted in the whole graph. Compactness then assembles the robust seeds.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.BoundedLossCells

open Energy BoundedLoss
open scoped BigOperators symmDiff

variable {V : Type u} {ι : Type w} (G : SimpleGraph V) (owner : V → ι)

/-- The graph internal to one cell, leaving all other vertices isolated. -/
def cellGraph (i : ι) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ owner x = i ∧ owner y = i
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

def localLow (i : ι) : Set V := {x | (G.neighborSet x).Finite ∧ owner x = i}

def localHubs (i : ι) : Set V := {x | (G.neighborSet x).Infinite ∧ owner x = i}

/-- Both orientations of exterior edges incident with a low vertex of the cell. -/
def interface (i : ι) : Set (V × V) :=
  {e | G.Adj e.1 e.2 ∧ ((e.1 ∈ localLow G owner i ∧ owner e.2 ≠ i) ∨
    (e.2 ∈ localLow G owner i ∧ owner e.1 ≠ i))}

private theorem finite_local (i : ι) (x : V) (hx : x ∈ localLow G owner i) :
    ((cellGraph G owner i).neighborSet x).Finite :=
  hx.1.subset fun _ h => h.1

private theorem gain_local_le (i : ι) (hI : (interface G owner i).Finite)
    (c : V → Bool) (F : Finset V) (hF : (F : Set V) ⊆ localLow G owner i) :
    gain (cellGraph G owner i) c F ≤ gain G c F + (hI.toFinset.card : ℤ) := by
  classical
  let J := cellGraph G owner i
  have hf := incident_finite G F (fun x hx => (hF hx).1)
  let E := hf.toFinset ∪ hI.toFinset
  have hE (e : V × V) (he : e ∈ incident G F) : e ∈ E :=
    Finset.mem_union_left _ (hf.mem_toFinset.mpr he)
  have hJG (e : V × V) (he : e ∈ incident J F) : e ∈ incident G F := ⟨he.1.1, he.2⟩
  have hg (A : SimpleGraph V) (hA : incident A F ⊆ incident G F) :
      gain A c F = ∑ e ∈ E, edgeDelta A c (flip c F) e :=
    finsum_eq_sum_of_support_subset _ (fun e he =>
      hE e (hA (support_edgeDelta_flip_subset A c F he)))
  have hpt (e : V × V) : edgeDelta J c (flip c F) e ≤ edgeDelta G c (flip c F) e +
      (if e ∈ hI.toFinset then 1 else 0) := by
    by_cases he : e ∈ incident G F
    case neg =>
      have z (A : SimpleGraph V) (hn : e ∉ incident A F) : edgeDelta A c (flip c F) e = 0 :=
        Classical.byContradiction fun h => hn (support_edgeDelta_flip_subset A c F h)
      rw [z G he, z J (fun h => he (hJG e h))]
      split_ifs <;> decide
    by_cases ha : J.Adj e.1 e.2
    case pos =>
      simp only [edgeDelta, if_pos ha, if_pos he.1]
      split_ifs <;> omega
    have hi : e ∈ hI.toFinset := hI.mem_toFinset.mpr ⟨he.1, he.2.elim
      (fun hx => Or.inl ⟨hF hx, fun hy => ha ⟨he.1, (hF hx).2, hy⟩⟩)
      (fun hy => Or.inr ⟨hF hy, fun hx => ha ⟨he.1, hx, (hF hy).2⟩⟩)⟩
    simp only [edgeDelta, if_neg ha, if_pos he.1, if_pos hi, cutIndicator]
    split_ifs <;> decide
  rw [hg J (fun e he => hJG e he), hg G Set.Subset.rfl]
  have hsum := Finset.sum_le_sum (s := E) (fun e _ => hpt e)
  rw [Finset.sum_add_distrib] at hsum
  have he : E.filter (· ∈ hI.toFinset) = hI.toFinset := Finset.ext fun x =>
    Finset.mem_filter.trans ⟨And.right, fun hx => ⟨Finset.mem_union_right _ hx, hx⟩⟩
  simpa only [Finset.sum_boole, he] using hsum

/-- Finite-volume optimizers lying in a common compact family give a
strongly maximal colouring in that family. -/
theorem strongMaximal_in_compact_of_finite [TopologicalSpace Bool] [DiscreteTopology Bool]
    (A : Set V) (K : Set (V → Bool)) (hK : IsCompact K)
    (hfinite : ∀ U : Finset V, (U : Set V) ⊆ A →
      ∃ q ∈ K, StrongMaximal G (U : Set V) q) :
    ∃ q ∈ K, StrongMaximal G A q := by
  classical
  let I := {U : Finset V // (U : Set V) ⊆ A}
  let P (i : I) : Set (V → Bool) := {q | StrongMaximal G (i.val : Set V) q}
  have hclosed (i : I) : IsClosed (P i) := StrongTopology.isClosed_strongMaximal G _
  have hF (F : Finset I) : (K ∩ ⋂ i ∈ F, P i).Nonempty := by
    let U := F.biUnion (fun i => i.val)
    have hU : (U : Set V) ⊆ A := fun _ hx =>
      let ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
      i.property hi
    obtain ⟨q, hq, hm⟩ := hfinite U hU
    exact ⟨q, hq, Set.mem_iInter₂.mpr fun i hi S hS hf => hm S
      (fun _ hx => Finset.mem_biUnion.mpr ⟨i, hi, hS hx⟩) hf⟩
  obtain ⟨q, hq, hstrong⟩ := hK.inter_iInter_nonempty P hclosed hF
  exact ⟨q, hq, fun S hS hf => (Set.mem_iInter.mp hstrong (⟨S, hS⟩ : I)) S Set.Subset.rfl hf⟩

open Classical in
/-- Read the global colouring on the chosen cell and the seed elsewhere. -/
noncomputable def project (seed : ι → V → Bool) (i : ι) (q : V → Bool) (x : V) : Bool :=
  if owner x = i then q x else seed i x

private theorem continuous_project [TopologicalSpace Bool] (seed : ι → V → Bool) (i : ι) :
    Continuous (project owner seed i) := by
  classical
  exact continuous_pi fun x =>
    if hx : owner x = i then by simpa [project, hx] using
      (continuous_apply x : Continuous (fun q : V → Bool => q x))
    else by simpa [project, hx] using (continuous_const (y := seed i x) (X := V → Bool))

private theorem projected_flip (seed : ι → V → Bool) (i : ι) (q : V → Bool) (U : Finset V)
    (hU : ∀ x ∈ U, (G.neighborSet x).Finite)
    (hfix : Set.EqOn q (fun x => seed (owner x) x) (U : Set V)ᶜ) :
    ∃ F : Finset V, F ⊆ U ∧ (F : Set V) ⊆ localLow G owner i ∧
      project owner seed i q = flip (seed i) F := by
  classical
  let F := U.filter fun x => owner x = i ∧ q x ≠ seed i x
  refine ⟨F, Finset.filter_subset .., fun x hx =>
    ⟨hU x (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩, ?_⟩
  funext x
  by_cases hxi : owner x = i
  · have hmem : x ∈ F ↔ q x ≠ seed i x := Finset.mem_filter.trans
      ⟨fun h => h.2.2, fun hn => ⟨Classical.byContradiction (fun hxU =>
        hn ((hfix hxU).trans (congrArg (fun j => seed j x) hxi))), hxi, hn⟩⟩
    cases hq : q x <;> cases hs : seed i x <;> simp [project, Energy.flip, hxi, hmem, hq, hs]
  · have hn : x ∉ F := fun hx => hxi (Finset.mem_filter.mp hx).2.1
    simp [project, Energy.flip, hxi, hn]

/-- Every finite global optimizer stays in each cell's bounded-loss orbit
when read against that cell's original seed. -/
theorem project_mem_orbit (seed : ι → V → Bool) (i : ι) (hI : (interface G owner i).Finite)
    (q : V → Bool) (U : Finset V) (hU : ∀ x ∈ U, (G.neighborSet x).Finite)
    (hfix : Set.EqOn q (fun x => seed (owner x) x) (U : Set V)ᶜ)
    (hm : StrongMaximal G (U : Set V) q) :
    project owner seed i q ∈ orbit (cellGraph G owner i) (localLow G owner i)
      (seed i) hI.toFinset.card := by
  classical
  obtain ⟨F, hFU, hF, heq⟩ := projected_flip G owner seed i q U hU hfix
  refine ⟨F, hF, ?_, heq⟩
  let J := cellGraph G owner i
  have hf (x : V) (hx : x ∈ F) : (J.neighborSet x).Finite :=
    finite_local G owner i x (hF hx)
  have hg := hm F (fun _ hx => hFU hx) (fun x hx => (hF hx).1)
  have hl := gain_local_le G owner i hI q F hF
  have hcong : gain J (project owner seed i q) F = gain J q F :=
    gain_congr_of_incident_eq J _ _ F fun e he => ⟨if_pos he.1.2.1, if_pos he.1.2.2⟩
  have hsum := gain_symmDiff J (seed i) F F hf hf
  rw [symmDiff_self, Finset.bot_eq_empty, gain_empty, ← heq, hcong] at hsum
  change gain J q F ≤ _ at hl
  change -((hI.toFinset.card : ℕ) : ℤ) ≤ gain J (seed i) F
  omega

/-- Finite hub groups supported inside their own cells allow a strong
solution when each cell has only finitely many exterior low incidences. -/
theorem exists_strong_solution (hH : ∀ i, (localHubs G owner i).Finite)
    (hN : ∀ i h, h ∈ localHubs G owner i → (G.neighborSet h ∩ localLow G owner i).Infinite)
    (hI : ∀ i, (interface G owner i).Finite) :
    ∃ q, StrongMaximal G {x | (G.neighborSet x).Finite} q ∧
      ∀ h, (G.neighborSet h).Infinite → (oppositeSet G q h).Infinite := by
  classical
  let : TopologicalSpace Bool := ⊥
  let : DiscreteTopology Bool := ⟨rfl⟩
  have hseed (i : ι) : ∃ c, ∀ h ∈ localHubs G owner i,
      Robust (cellGraph G owner i) (localLow G owner i) c h := by
    have hH' (h : V) (hh : h ∈ localHubs G owner i) : h ∉ localLow G owner i ∧
        ((cellGraph G owner i).neighborSet h ∩ localLow G owner i).Infinite :=
      ⟨fun hx => hh.1 hx.1, (hN i h hh).mono fun _ hy => ⟨⟨hy.1, hh.2, hy.2.2⟩, hy.2⟩⟩
    obtain ⟨c, _, hc⟩ := exists_robust_seed (cellGraph G owner i) (localLow G owner i)
      (localHubs G owner i) (hH i) (finite_local G owner i) hH'
    exact ⟨c, hc⟩
  choose seed hs using hseed
  let window (i : ι) := closure (orbit (cellGraph G owner i) (localLow G owner i)
    (seed i) (hI i).toFinset.card)
  let K := ⋂ i, project owner seed i ⁻¹' window i
  have hK : IsClosed K := isClosed_iInter fun i =>
    isClosed_closure.preimage (continuous_project owner seed i)
  have hfinite (U : Finset V) (hU : ∀ x ∈ U, (G.neighborSet x).Finite) :
      ∃ q ∈ K, StrongMaximal G (U : Set V) q := by
    obtain ⟨q, hq, hm⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
      (U : Set V)ᶜ (fun x => seed (owner x) x)
    have hmax : StrongMaximal G (U : Set V) q := by simpa using hm
    exact ⟨q, Set.mem_iInter.mpr fun i =>
      subset_closure (project_mem_orbit G owner seed i (hI i) q U hU hq hmax), hmax⟩
  obtain ⟨q, hq, hm⟩ := strongMaximal_in_compact_of_finite G
    {x | (G.neighborSet x).Finite} K hK.isCompact (fun U hU => hfinite U (fun _ hx => hU hx))
  refine ⟨q, hm, fun h hh => ?_⟩
  let i := owner h
  have hloc := hs i h ⟨hh, rfl⟩ (Int.ofNat (hI i).toFinset.card)
    (project owner seed i q) (Set.mem_iInter.mp hq i)
  refine hloc.mono fun y hy => ⟨hy.1.1.1, ?_⟩
  have hhcell : owner h = i := rfl
  simpa [project, hy.2.2, hhcell, i] using hy.1.2

/-- A countable graph with a finite interface around each cell has an
unfriendly partition and wins the partitioning game at every ordinal clock. -/
theorem mission [Countable V] (hH : ∀ i, (localHubs G owner i).Finite)
    (hN : ∀ i h, h ∈ localHubs G owner i → (G.neighborSet h ∩ localLow G owner i).Infinite)
    (hI : ∀ i, (interface G owner i).Finite) :
    (∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) ∧
      ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α := by
  obtain ⟨q, hm, hg⟩ := exists_strong_solution G owner hH hN hI
  have huf : ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x :=
    ⟨fun x => some (q x), fun x => (Classical.em (G.neighborSet x).Finite).elim
      (fun hx => unfriendlyAt_of_strongMaximal G _ q hm x hx hx)
      (fun hx => unfriendly_of_infinite_opposite G q x (hg x hx))⟩
  exact ⟨huf, all_clocks_of_global G huf⟩


end TenChallenges.Continuation.BoundedLossCells

theorem solution {V : Type u} {ι : Type w} [Countable V]
    (G : SimpleGraph V) (owner : V → ι)
    (hH : ∀ i, {x : V | (G.neighborSet x).Infinite ∧ owner x = i}.Finite)
    (hN : ∀ i h, (G.neighborSet h).Infinite ∧ owner h = i →
      (G.neighborSet h ∩ {x : V | (G.neighborSet x).Finite ∧ owner x = i}).Infinite)
    (hI : ∀ i, {e : V × V | G.Adj e.1 e.2 ∧
      (((G.neighborSet e.1).Finite ∧ owner e.1 = i) ∧ owner e.2 ≠ i ∨
       ((G.neighborSet e.2).Finite ∧ owner e.2 = i) ∧ owner e.1 ≠ i)}.Finite) :
    (∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) ∧
      ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r :=
  TenChallenges.Continuation.BoundedLossCells.mission G owner hH hN hI

#print axioms solution
