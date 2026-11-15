-- Prove2me | solution 1 for TenChallenges.challenge_10_infiniteCore
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T21:51:39.254121+00:00
-- url     : https://prove2.me/submissions/38ff8d62-0f32-4b33-9171-bff3038eb323

import Definitions.Def_TenChallenges_Challenge_10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete

set_option linter.style.haveILetI false
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
  letI : TopologicalSpace Bool := ⊥
  letI : DiscreteTopology Bool := ⟨rfl⟩
  letI : CompactSpace (V → Bool) := inferInstance
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
  haveI : Infinite (NeighColored G (fun w => some (c w)) v (some (!(c v)))) :=
    Set.infinite_coe_iff.mpr ((oppositeSet_eq_colored G c v) ▸ hO)
  haveI : Countable (NeighColored G (fun w => some (c w)) v (some (c v))) :=
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
  haveI : Finite (NeighColored G (fun w => some (c w)) v (some (!(c v)))) :=
    Set.finite_coe_iff.mpr ((oppositeSet_eq_colored G c v) ▸ hOfin)
  obtain ⟨e⟩ := (Cardinal.le_def ..).mp hcard
  haveI : Finite (NeighColored G (fun w => some (c w)) v (some (c v))) :=
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

/- Inlined from Continuation/UnfriendlyEnergyBound.lean. -/
/-!
# A uniform bound after changing one boundary color

Only finite-degree repair supports enter the energy sums. The singleton boundary
vertex may have infinite degree; no energy identity is applied to its singleton.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators symmDiff

variable {V : Type u}

open Classical in
/-- Both orientations of pairs joining `v` to the finite opposite-neighbor cover. -/
noncomputable def oppositePairs (v : V) (O : Finset V) : Finset (V × V) :=
  O.image (fun w => (v, w)) ∪ O.image (fun w => (w, v))

open Classical in
/-- A pointwise allowance for the positive effect of a boundary singleton flip. -/
noncomputable def pairAllowance (v : V) (O : Finset V) (e : V × V) : ℤ :=
  if e ∈ oppositePairs v O then 2 else 0

private theorem edgeDelta_bounds (G : SimpleGraph V) (c d : V → Bool) (e : V × V) :
    -1 ≤ edgeDelta G c d e ∧ edgeDelta G c d e ≤ 1 := by
  unfold edgeDelta cutIndicator
  split_ifs
  all_goals omega

open Classical in
private theorem same_of_not_oppositePairs (G : SimpleGraph V) (c : V → Bool)
    (v : V) (O : Finset V)
    (hO : ∀ w, G.Adj v w → c w ≠ c v → w ∈ O)
    (x y : V) (ha : G.Adj x y) (hr : (x, y) ∉ oppositePairs v O)
    (ht : x = v ∨ y = v) : c x = c y :=
  Classical.byContradiction (fun hn => ht.elim
    (fun hx => hr (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨y, hO y (hx ▸ ha) (fun hc => hn ((congrArg c hx).trans hc.symm)),
        Prod.ext hx.symm rfl⟩)))
    (fun hy => hr (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨x, hO x (hy ▸ ha.symm) (fun hc => hn (hc.trans (congrArg c hy).symm)),
        Prod.ext rfl hy.symm⟩))))

private theorem edgeDelta_singleton_le_of_same (G : SimpleGraph V) (c : V → Bool)
    (v : V) (S : Finset V) (hvS : v ∉ S) (x y : V)
    (hsame : G.Adj x y → (x = v ∨ y = v) → c x = c y) :
    edgeDelta G (flip c {v}) (flip (flip c {v}) S) (x, y) ≤
      edgeDelta G c (flip c S) (x, y) := by
  classical
  by_cases ha : G.Adj x y
  all_goals by_cases hx : x = v
  all_goals by_cases hy : y = v
  all_goals by_cases hxS : x ∈ S
  all_goals by_cases hyS : y ∈ S
  all_goals simp_all [edgeDelta, cutIndicator, flip]

/-- Only pairs to original opposite-colored neighbors can contribute positive perturbation. -/
theorem edgeDelta_singleton_le (G : SimpleGraph V) (c : V → Bool)
    (v : V) (S O : Finset V) (hvS : v ∉ S)
    (hO : ∀ w, G.Adj v w → c w ≠ c v → w ∈ O) (e : V × V) :
    edgeDelta G (flip c {v}) (flip (flip c {v}) S) e ≤
      edgeDelta G c (flip c S) e + pairAllowance v O e := by
  classical
  by_cases he : e ∈ oppositePairs v O
  · have hb := And.intro (edgeDelta_bounds G (flip c {v}) (flip (flip c {v}) S) e).2
        (edgeDelta_bounds G c (flip c S) e).1
    simp only [pairAllowance, if_pos he]
    omega
  · simpa only [pairAllowance, if_neg he, add_zero] using
      edgeDelta_singleton_le_of_same G c v S hvS e.1 e.2
        (fun ha ht => same_of_not_oppositePairs G c v O hO e.1 e.2 ha he ht)

private theorem pairAllowance_sum (v : V) (O : Finset V) (U : Finset (V × V))
    (hRU : oppositePairs v O ⊆ U) :
    (∑ e ∈ U, pairAllowance v O e) = 2 * ((oppositePairs v O).card : ℤ) := by
  classical
  simp [pairAllowance, Finset.inter_eq_right.mpr hRU, mul_comm]

open Classical in
private theorem oppositePairs_card_le (v : V) (O : Finset V) :
    (oppositePairs v O).card ≤ 2 * O.card :=
  (Finset.card_union_le ..).trans
    ((Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans_eq (two_mul O.card).symm)

/-- Changing an external boundary vertex raises any admissible repair gain by at most `4|O|`. -/
theorem gain_singleton_perturbation_le (G : SimpleGraph V) (c : V → Bool)
    (v : V) (S O : Finset V) (hvS : v ∉ S)
    (hS : ∀ x ∈ S, (G.neighborSet x).Finite)
    (hO : ∀ w, G.Adj v w → c w ≠ c v → w ∈ O) :
    gain G (flip c {v}) S ≤ gain G c S + 4 * (O.card : ℤ) := by
  classical
  let U := (incident_finite G S hS).toFinset ∪ oppositePairs v O
  have hsum (d : V → Bool) : gain G d S = ∑ e ∈ U, edgeDelta G d (flip d S) e :=
    finsum_eq_sum_of_support_subset _ (fun e he => Finset.mem_union_left _
      ((incident_finite G S hS).mem_toFinset.mpr (support_edgeDelta_flip_subset G d S he)))
  have hle := Finset.sum_le_sum (s := U)
    (fun e (_ : e ∈ U) => edgeDelta_singleton_le G c v S O hvS hO e)
  rw [Finset.sum_add_distrib, pairAllowance_sum v O U Finset.subset_union_right,
    ← hsum (flip c {v}), ← hsum c] at hle
  have hcard := oppositePairs_card_le v O
  omega

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

/- Inlined from Continuation/UnfriendlyRepair.lean. -/
/-!
# Finite repair of strong cut maximality after a boundary flip

A strongly maximal coloring can be repaired within its maximality domain after
changing an external vertex with only finitely many original opposite neighbors.
The result uses neither countability nor finite degree of the changed vertex.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped symmDiff

variable {V : Type u}

/-- A finite opposite-neighbor cover bounds the repair needed after an external singleton flip. -/
theorem exists_strongMaximal_repair (G : SimpleGraph V) (A : Set V) (c : V → Bool)
    (hc : StrongMaximal G A c) (v : V) (hv : v ∉ A) (O : Finset V)
    (hO : ∀ w, G.Adj v w → c w ≠ c v → w ∈ O) :
    ∃ S : Finset V, (S : Set V) ⊆ A ∧
      (∀ x ∈ S, (G.neighborSet x).Finite) ∧
      StrongMaximal G A (flip (flip c {v}) S) := by
  classical
  let allowed : Finset V → Prop := fun S =>
    (S : Set V) ⊆ A ∧ ∀ x ∈ S, (G.neighborSet x).Finite
  have hempty : allowed ∅ := by simp [allowed]
  have hclosed : ∀ S T, allowed S → allowed T → allowed (S ∆ T) :=
    fun S T hS hT =>
      ⟨fun x hx => (Finset.mem_symmDiff.mp hx).elim
        (fun h => hS.1 h.1) (fun h => hT.1 h.1),
        fun x hx => (Finset.mem_symmDiff.mp hx).elim
          (fun h => hS.2 x h.1) (fun h => hT.2 x h.1)⟩
  have hbound : ∀ S, allowed S → gain G (flip c {v}) S ≤ 4 * (O.card : ℤ) :=
    fun S hS => (gain_singleton_perturbation_le G c v S O
      (fun hvin => hv (hS.1 hvin)) hS.2 hO).trans
        ((Int.add_le_add_right (hc S hS.1 hS.2) (4 * (O.card : ℤ))).trans_eq (zero_add _))
  obtain ⟨S, hS, hstable⟩ :=
    TenChallenges.Continuation.FiniteRepair.exists_stable_flip allowed hempty hclosed
      flip (gain G) (fun d S T hS hT => gain_symmDiff G d S T hS.2 hT.2)
      (flip c {v}) (4 * (O.card : ℤ)) hbound
  exact ⟨S, hS.1, hS.2, fun T hTA hTN => hstable T ⟨hTA, hTN⟩⟩

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyBoundaryExtension.lean. -/
/-!
# Unfriendly extensions across a boundary

A prescribed coloring on any boundary extends to a coloring unfriendly outside
that boundary, provided only finitely many infinite-degree vertices remain
outside it. No assertion is made about unfriendly inequalities on the boundary.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

variable {V : Type u}

private theorem finite_hub_stage_eqOn [Countable V] (G : SimpleGraph V)
    (A D : Set V) (hDA : D ⊆ Aᶜ) (c0 : V → Bool)
    (hc0 : StrongMaximal G A c0) (F : Finset V)
    (hF : ∀ v ∈ F, (G.neighborSet v).Infinite ∧ v ∉ A ∧ v ∉ D) :
    ∃ c, Set.EqOn c c0 D ∧ StrongMaximal G A c ∧
      ∀ v ∈ F, (oppositeSet G c v).Infinite := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty => exact fun _ => ⟨c0, fun _ _ => rfl, hc0,
      fun w hw => (Finset.notMem_empty w hw).elim⟩
  | @insert v F hvF ih =>
    intro hF
    obtain ⟨c, hcD, hc, hgood⟩ := ih (fun w hw => hF w (Finset.mem_insert_of_mem hw))
    obtain ⟨hNv, hvA, hvD⟩ := hF v (Finset.mem_insert_self v F)
    by_cases hOpp : (oppositeSet G c v).Infinite
    · exact ⟨c, hcD, hc, fun w hw => (Finset.mem_insert.mp hw).elim
        (fun hwv => hwv.symm ▸ hOpp) (fun hwF => hgood w hwF)⟩
    · have hO : (oppositeSet G c v).Finite := Set.not_infinite.mp hOpp
      have hbad : ¬ UnfriendlyAt G (fun w => some (c w)) v :=
        fun hUF => hOpp (infinite_opposite_of_unfriendly G c v hNv hUF)
      obtain ⟨S, hSA, _, hstable⟩ := exists_strongMaximal_repair G A c hc v hvA
        hO.toFinset (fun w ha hne => hO.mem_toFinset.mpr ⟨ha, hne⟩)
      have hfix : Set.EqOn (flip (flip c {v}) S) c D := fun w hw =>
        (if_neg (show w ∉ S from fun hwS => hDA hw (hSA hwS))).trans
          (if_neg (show w ∉ ({v} : Finset V) from
            fun hwv => hvD ((Finset.mem_singleton.mp hwv) ▸ hw)))
      have hnew : (oppositeSet G (flip (flip c {v}) S) v).Infinite :=
        infinite_opposite_flip G (flip c {v}) v S (fun hvS => hvA (hSA hvS))
          (infinite_opposite_flip_bad G c v hNv hbad)
      have hold : ∀ w ∈ F, (oppositeSet G (flip (flip c {v}) S) w).Infinite := fun w hw =>
        infinite_opposite_flip G (flip c {v}) w S
          (fun hwS => (hF w (Finset.mem_insert_of_mem hw)).2.1 (hSA hwS))
          (infinite_opposite_flip G c w {v}
            (fun hwv => hvF ((Finset.mem_singleton.mp hwv) ▸ hw)) (hgood w hw))
      exact ⟨flip (flip c {v}) S, fun w hw => (hfix hw).trans (hcD hw), hstable,
        fun w hw => (Finset.mem_insert.mp hw).elim
          (fun hwv => hwv.symm ▸ hnew) (fun hwF => hold w hwF)⟩

/-- Arbitrary boundary colors extend to an unfriendly coloring off the boundary
when only finitely many infinite-degree vertices remain off it. -/
theorem exists_unfriendly_extension [Countable V] (G : SimpleGraph V)
    (D : Set V) (p : V → Bool)
    (hI : {v : V | v ∉ D ∧ (G.neighborSet v).Infinite}.Finite) :
    ∃ c : V → Bool, Set.EqOn c p D ∧
      ∀ v, v ∉ D → UnfriendlyAt G (fun w => some (c w)) v := by
  classical
  let I : Set V := {v | v ∉ D ∧ (G.neighborSet v).Infinite}
  obtain ⟨c0, hc0, hm0⟩ :=
    StrongMaximalCompactness.exists_strongMaximal_eqOn G (D ∪ I) p
  obtain ⟨c, hcD, hm, hgood⟩ := finite_hub_stage_eqOn G (D ∪ I)ᶜ D
    (fun _ hd hnot => hnot (Or.inl hd)) c0 hm0 hI.toFinset
    (fun w hw =>
      let hi := hI.mem_toFinset.mp hw
      ⟨hi.2, fun hnot => hnot (Or.inr hi), hi.1⟩)
  refine ⟨c, fun w hw => (hcD hw).trans (hc0 (Or.inl hw)), fun w hw => ?_⟩
  exact (Classical.em (G.neighborSet w).Finite).elim
    (fun hN => unfriendlyAt_of_strongMaximal G (D ∪ I)ᶜ c hm w
      (fun hi => hi.elim hw (fun hiI => hiI.2 hN)) hN)
    (fun hN => unfriendly_of_infinite_opposite G c w
      (hgood w (hI.mem_toFinset.mpr ⟨hw, Set.not_finite.mp hN⟩)))

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
  letI : Finite S := hS.to_subtype
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
  · letI : Fintype (NeighColored G p v (some (!b))) := hO.fintype
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
  · haveI : Infinite (NeighColored G p v (some (!b))) := Set.infinite_coe_iff.mpr hO
    haveI : Countable (NeighColored G p v (some b)) :=
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

/- Inlined from Continuation/Challenge10Next.lean. -/
set_option linter.all false


namespace Continuation.TC10
open Classical SimpleGraph
open scoped Cardinal
variable {V : Type u} (G : SimpleGraph V)

/-- Every colored vertex is currently unfriendly. -/
def Stable (f : V → Option Bool) : Prop :=
  ∀ x b, f x = some b → UnfriendlyAt G f x

/-- Two simple shapes of a partial coloring which can safely accommodate one more query. -/
def Ready (f : V → Option Bool) : Prop :=
  ((∀ x b, f x = some b → b = false) ∧
    ∀ x y, f x = some false → f y = some false → ¬ G.Adj x y) ∨
  ((∀ b, (f ⁻¹' {some b}).Subsingleton) ∧
    ∀ x b, f x = some b → ∃ y, G.Adj x y ∧ f y = some (!b))

lemma neigh_update {f : V → Option Bool} (x : V) (b c : Bool) :
    #(NeighColored G (Function.update f x (some b)) x (some c)) =
      #(NeighColored G f x (some c)) := by
  apply Cardinal.mk_congr
  exact Equiv.subtypeEquivRight fun y => and_congr_right fun hy => by
    simp only [Set.mem_preimage, Function.update_of_ne (G.ne_of_adj hy).symm]

lemma no_same {f : V → Option Bool} {x : V} (b : Bool)
    (hfx : f x = some b) (hno : ∀ y, G.Adj x y → f y ≠ some b) :
    UnfriendlyAt G f x := by
  refine ⟨b, hfx, ?_⟩
  have hempty : IsEmpty (NeighColored G f x (some b)) :=
    ⟨fun ⟨y, hy⟩ => hno y hy.1 hy.2⟩
  exact (@Cardinal.mk_eq_zero (NeighColored G f x (some b)) hempty).symm ▸ zero_le

lemma unique_same {f : V → Option Bool} {x : V} (b : Bool)
    (hfx : f x = some b)
    (hsame : (G.neighborSet x ∩ f ⁻¹' {some b}).Subsingleton)
    (hopp : ∃ y, G.Adj x y ∧ f y = some (!b)) :
    UnfriendlyAt G f x := by
  refine ⟨b, hfx, hsame.cardinalMk_le_one.trans ?_⟩
  exact Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero_iff.mpr
    (let ⟨y, hya, hyc⟩ := hopp; ⟨⟨y, hya, hyc⟩⟩))

lemma minority_update (f : V → Option Bool) (x : V) :
    ∃ b, UnfriendlyAt G (Function.update f x (some b)) x := by
  rcases le_total #(NeighColored G f x (some false)) #(NeighColored G f x (some true)) with h | h
  · exact ⟨false, false, by simp, by simpa only [neigh_update, Bool.not_false] using h⟩
  · exact ⟨true, true, by simp, by simpa only [neigh_update, Bool.not_true] using h⟩

lemma update_extends {f : V → Option Bool} {x : V} (hx : f x = none) (b : Bool) :
    Extends f (Function.update f x (some b)) := by
  intro y c hfy
  have hyx : y ≠ x := fun heq => by simpa [heq, hx] using hfy
  simpa only [Function.update_of_ne hyx] using hfy

lemma finite_update {f : V → Option Bool} (hf : HasFiniteDomain f) (x : V) (b : Bool) :
    HasFiniteDomain (Function.update f x (some b)) := by
  exact (hf.insert x).subset (fun y hy => (eq_or_ne y x).elim
    (fun h => Or.inl h)
    (fun h => Or.inr (by simpa only [Set.mem_setOf_eq, Function.update_of_ne h] using hy)))

lemma wins_zero (f : V → Option Bool) : PartitionerWins G f (0 : Ordinal.{v}) := by
  rw [PartitionerWins]
  exact fun _ _ h => (not_lt_zero h).elim


lemma stable_wins_one {f : V → Option Bool} (hf : HasFiniteDomain f) (hs : Stable G f) :
    PartitionerWins G f (1 : Ordinal.{v}) := by
  classical
  rw [PartitionerWins]
  intro x β hβ
  obtain rfl := Order.lt_one_iff.mp hβ
  exact (Classical.em (f x = none)).elim
    (fun hx => let ⟨b, hb⟩ := minority_update G f x
      ⟨Function.update f x (some b),
        ⟨update_extends hx b, finite_update hf x b, hb⟩, wins_zero G _⟩)
    (fun hx => let ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hx
      ⟨f, ⟨fun _ _ h => h, hf, hs x b hb⟩, wins_zero G _⟩)

lemma ready_stable {f : V → Option Bool} (hr : Ready G f) : Stable G f := by
  intro x b hfx
  rcases hr with ⟨hc, hi⟩ | ⟨hs, ho⟩
  · exact no_same G b hfx (fun y hxy hfy =>
      hi x y (hc x b hfx ▸ hfx) (hc y b hfy ▸ hfy) hxy)
  · exact no_same G b hfx (fun y hxy hfy => G.ne_of_adj hxy (hs b hfx hfy))

lemma ready_update {f : V → Option Bool} (hr : Ready G f) {x : V}
    (hx : f x = none) : ∃ b, Stable G (Function.update f x (some b)) := by
  rcases hr with hind | hsparse
  · refine ⟨true, fun y c hy => no_same G c hy ?_⟩
    intro z hyz hz
    cases c
    · simp [Function.update_apply, ite_eq_iff] at hy hz
      exact hind.2 y z hy.2 hz.2 hyz
    · have htrue : ∀ w, f w ≠ some true := fun w hw => Bool.noConfusion (hind.1 w true hw)
      simp [Function.update_apply, ite_eq_iff, htrue] at hy hz
      exact G.ne_of_adj hyz (hy.trans hz.symm)
  · obtain ⟨b, hb⟩ := minority_update G f x
    refine ⟨b, fun y c hy => ?_⟩
    by_cases hyx : y = x
    · exact hyx.symm ▸ hb
    · refine unique_same G c hy ?_ ?_
      · refine (Set.subsingleton_singleton (a := x)).anti ?_
        intro z hz
        by_contra hzx
        exact G.ne_of_adj hz.1 (hsparse.1 c
          (by simpa only [Set.mem_preimage, Set.mem_singleton_iff, Function.update_of_ne hyx] using hy)
          (by simpa only [Set.mem_preimage, Set.mem_singleton_iff, Function.update_of_ne hzx] using hz.2))
      · obtain ⟨z, hzy, hz⟩ := hsparse.2 y c (by simpa only [Function.update_of_ne hyx] using hy)
        exact ⟨z, hzy, update_extends hx b z (!c) hz⟩

lemma ready_response {f : V → Option Bool} (hf : HasFiniteDomain f) (hr : Ready G f) (x : V) :
    ∃ g, IsLegalResponse G f g x ∧ Stable G g := by
  by_cases hx : f x = none
  · obtain ⟨b, hb⟩ := ready_update G hr hx
    exact ⟨_, ⟨update_extends hx b, finite_update hf x b, hb x b (by simp)⟩, hb⟩
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hx
    exact ⟨f, ⟨fun _ _ h => h, hf, ready_stable G hr x b hb⟩, ready_stable G hr⟩

noncomputable def first (a : V) : V → Option Bool :=
  Function.update (emptyPartition V) a (some false)

noncomputable def second (a b : V) : V → Option Bool :=
  Function.update (first a) b (some (if G.Adj a b then true else false))

lemma first_legal (a : V) : IsLegalResponse G (emptyPartition V) (first a) a := by
  refine ⟨update_extends rfl false,
    finite_update (by simp [HasFiniteDomain, emptyPartition]) a false,
    no_same G false (by simp [first]) ?_⟩
  intro y hay
  simp [first, Function.update_of_ne (G.ne_of_adj hay).symm, emptyPartition]

lemma second_legal_ready (a b : V) :
    IsLegalResponse G (first a) (second G a b) b ∧ Ready G (second G a b) := by
  have hr : Ready G (second G a b) := by
    by_cases hab : G.Adj a b
    · have hne := G.ne_of_adj hab
      have hfalse (x : V) : second G a b x = some false ↔ x = a := by
        simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition]
        exact fun e => e.symm ▸ hne
      have htrue (x : V) : second G a b x = some true ↔ x = b := by
        simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition]
      refine Or.inr ⟨?_, ?_⟩
      · intro c
        cases c
        · exact fun x hx y hy => (hfalse x).mp hx |>.trans ((hfalse y).mp hy).symm
        · exact fun x hx y hy => (htrue x).mp hx |>.trans ((htrue y).mp hy).symm
      · rintro x (_ | _) hx
        · exact ⟨b, ((hfalse x).mp hx).symm ▸ hab, (htrue b).mpr rfl⟩
        · exact ⟨a, ((htrue x).mp hx).symm ▸ hab.symm, (hfalse a).mpr rfl⟩
    · have hfalse (x : V) : second G a b x = some false ↔ x = b ∨ x = a := by
        simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition, imp_iff_not_or]
      refine Or.inl ⟨?_, ?_⟩
      · rintro x (_ | _) hx
        · rfl
        · simp [second, first, hab, Function.update_apply, ite_eq_iff, emptyPartition] at hx
      · intro x y hx hy
        rcases (hfalse x).mp hx with rfl | rfl
        all_goals rcases (hfalse y).mp hy with rfl | rfl
        all_goals simp_all [SimpleGraph.adj_comm]
  refine ⟨⟨?_, finite_update (first_legal G a).2.1 b (if G.Adj a b then true else false),
    ready_stable G hr b (if G.Adj a b then true else false) (by simp [second])⟩, hr⟩
  intro x c hx
  simp [first, Function.update_apply, emptyPartition, ite_eq_iff] at hx
  rcases hx with ⟨rfl, rfl⟩
  by_cases hxb : x = b <;> simp [second, first, hxb]


lemma wins_mono {f : V → Option Bool} {α β : Ordinal.{v}}
    (hβα : β ≤ α) (h : PartitionerWins G f α) : PartitionerWins G f β := by
  rw [PartitionerWins] at h ⊢
  exact fun x γ hγ => h x γ (hγ.trans_le hβα)


/-- Partitioner wins the four-round game on every simple graph, without a countability assumption. -/
theorem win_four : PartitionerWins G (emptyPartition V) (4 : Ordinal.{v}) := by
  rw [PartitionerWins]
  intro a α hα
  refine ⟨first a, first_legal G a,
    wins_mono G (Order.lt_succ_iff.mp ((congrArg (fun o : Ordinal.{v} => α < o) (Ordinal.natCast_succ 3)).mp hα)) ?_⟩
  rw [PartitionerWins]
  intro b β hβ
  refine ⟨second G a b, (second_legal_ready G a b).1,
    wins_mono G (Order.lt_succ_iff.mp
      ((congrArg (fun o : Ordinal.{v} => β < o) (Ordinal.natCast_succ 2)).mp hβ)) ?_⟩
  rw [PartitionerWins]
  intro c γ hγ
  obtain ⟨g, hg, hs⟩ := ready_response G (second_legal_ready G a b).1.2.1
    (second_legal_ready G a b).2 c
  exact ⟨g, hg, wins_mono G
    ((show ((1 : ℕ) : Ordinal.{v}) = 1 from Nat.cast_one) ▸ Order.lt_succ_iff.mp ((congrArg (fun o : Ordinal.{v} => γ < o)
      (Ordinal.natCast_succ 1)).mp hγ)) (stable_wins_one G hg.2.1 hs)⟩

end Continuation.TC10

/- Inlined from Continuation/UnfriendlyInfiniteDegree.lean. -/
/-!
# Unfriendly partition games on graphs of infinite degree

Every finite partial coloring admits a legal response at a vertex with infinitely
many neighbors. Consequently, when every neighborhood is infinite, Partitioner
wins for every ordinal clock from every finite partial coloring.
-/

open SimpleGraph
open scoped Cardinal


namespace Continuation.InfiniteDegree

variable {V : Type u} (G : SimpleGraph V)

/-- A colored vertex with infinitely many neighbors can be made unfriendly by a finite extension. -/
lemma legal_response_colored {f : V → Option Bool} (hf : HasFiniteDomain f)
    (x : V) (b : Bool) (hfx : f x = some b) (hx : (G.neighborSet x).Infinite) :
    ∃ g, IsLegalResponse G f g x := by
  classical
  let D : Set V := {y | f y ≠ none}
  letI : Fintype D := hf.fintype
  have hT : (G.neighborSet x \ D).Infinite := hx.sdiff hf
  let e : D ↪ ↥(G.neighborSet x \ D) :=
    ((Fintype.equivFin D).toEmbedding.trans Fin.valEmbedding).trans (hT.natEmbedding _)
  let S : Set V := Set.range fun d : D => (e d).val
  have hSf : S.Finite := Set.finite_range _
  have hS : S ⊆ G.neighborSet x \ D := fun y ⟨d, hd⟩ => hd ▸ (e d).property
  let g : V → Option Bool := fun y => if y ∈ S then some (!b) else f y
  have hExt : Extends f g := fun y c hy =>
    (if_neg (fun hs : y ∈ S => (hS hs).2
      (show y ∈ D from fun hn => Option.some_ne_none c (hy.symm.trans hn)))).trans hy
  have hgf : HasFiniteDomain g := (hf.union hSf).subset fun y hy =>
    if h : y ∈ S then Or.inr h else Or.inl
      (show f y ≠ none from fun hn => hy ((if_neg h).trans hn))
  have hxS : x ∉ S := fun h => G.irrefl (hS h).1
  have hsame : (G.neighborSet x ∩ g ⁻¹' {some b}) ⊆ D := fun y hy =>
    if h : y ∈ S then False.elim ((Bool.not_eq_self b).mp
      (Option.some.inj ((if_pos h).symm.trans hy.2)))
    else fun hn => Option.some_ne_none b (hy.2.symm.trans ((if_neg h).trans hn))
  let E : D ↪ NeighColored G g x (some (!b)) :=
    ⟨fun d => ⟨(e d).val, (e d).property.1, if_pos ⟨d, rfl⟩⟩,
      fun d d' h => e.injective (Subtype.ext
        (congrArg (fun z : NeighColored G g x (some (!b)) => z.val) h))⟩
  exact ⟨g, hExt, hgf, b, (if_neg hxS).trans hfx,
    (Cardinal.mk_le_mk_of_subset hsame).trans ((Cardinal.le_def ..).mpr ⟨E⟩)⟩

/-- Every query at a vertex of infinite degree admits a finite legal response. -/
theorem legal_response {f : V → Option Bool} (hf : HasFiniteDomain f)
    (x : V) (hx : (G.neighborSet x).Infinite) :
    ∃ g, IsLegalResponse G f g x := by
  classical
  exact match hfx : f x with
    | some b => legal_response_colored G hf x b hfx hx
    | none =>
      let ⟨g, hg⟩ := legal_response_colored G (TC10.finite_update hf x false)
        x false (Function.update_self ..) hx
      ⟨g, ⟨fun y c hy => hg.1 y c (TC10.update_extends hfx false y c hy), hg.2⟩⟩

/-- No countability assumption is needed when all neighborhoods are infinite. -/
theorem partitionerWins_of_infinite_neighbors
    (hG : ∀ x, (G.neighborSet x).Infinite) (α : Ordinal.{v})
    {f : V → Option Bool} (hf : HasFiniteDomain f) : PartitionerWins G f α := by
  induction α using WellFoundedLT.induction generalizing f
  rename_i α ih
  rw [PartitionerWins]
  exact fun x β hβ => let ⟨g, hg⟩ := legal_response G hf x (hG x)
    ⟨g, hg, ih β hβ hg.2.1⟩

/-- Partitioner wins at every clock on a graph of infinite degree at every vertex. -/
theorem partitionerWins_empty_of_infinite_neighbors
    (hG : ∀ x, (G.neighborSet x).Infinite) (α : Ordinal.{v}) :
    PartitionerWins G (emptyPartition V) α :=
  partitionerWins_of_infinite_neighbors G hG α
    (by simp [HasFiniteDomain, emptyPartition])

end Continuation.InfiniteDegree

/- Inlined from Continuation/UnfriendlyCoreExtension.lean. -/
/-!
# Extending an infinite-degree core

A countable graph has an unfriendly partition if it has an induced subgraph
of infinite minimum degree and only finitely many infinite-degree vertices
outside that subgraph. This is a special case, not the unrestricted conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

variable {V : Type u}

private theorem infinite_induced_neighbors (G : SimpleGraph V) (R : Set V)
    (hR : ∀ v ∈ R, (G.neighborSet v ∩ R).Infinite) :
    ∀ x : R, ((G.induce R).neighborSet x).Infinite := by
  intro x
  apply Set.Infinite.of_image (Subtype.val : R → V)
  simpa [SimpleGraph.neighborSet_induce, Set.image_preimage_eq_inter_range] using
    hR x.val x.property

private theorem exists_boolean_unfriendly [Countable V] (G : SimpleGraph V)
    (hG : ∀ x, (G.neighborSet x).Infinite) :
    ∃ c : V → Bool, ∀ x, UnfriendlyAt G (fun w => some (c w)) x := by
  obtain ⟨p, hp⟩ := (unfriendly_partition_iff_all_clocks G).mpr
    (fun α => _root_.Continuation.InfiniteDegree.partitionerWins_empty_of_infinite_neighbors
      G hG α)
  let c : V → Bool := fun x => (p x).getD false
  have hpc : p = fun x => some (c x) := by
    funext x
    obtain ⟨b, hb, _⟩ := hp x
    simp [c, hb]
  exact ⟨c, hpc ▸ hp⟩

/-- An infinite-minimum-degree core absorbs finitely many exceptional hubs. -/
theorem exists_unfriendly_of_infinite_core [Countable V] (G : SimpleGraph V)
    (R : Set V) (hR : ∀ v ∈ R, (G.neighborSet v ∩ R).Infinite)
    (hOutside : {v : V | v ∉ R ∧ (G.neighborSet v).Infinite}.Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  classical
  obtain ⟨cR, hcR⟩ := exists_boolean_unfriendly (G.induce R)
    (infinite_induced_neighbors G R hR)
  let p0 : V → Bool := fun w => if hw : w ∈ R then cR ⟨w, hw⟩ else false
  obtain ⟨c, hfix, hout⟩ := Energy.exists_unfriendly_extension G R p0 hOutside
  have hc : ∀ x : R, c x.val = cR x := fun x =>
    (hfix x.property).trans (dif_pos x.property)
  refine ⟨fun w => some (c w), fun v => ?_⟩
  by_cases hv : v ∈ R
  · apply Energy.unfriendly_of_infinite_opposite G c v
    have hi := Energy.infinite_opposite_of_unfriendly (G.induce R) cR ⟨v, hv⟩
      (infinite_induced_neighbors G R hR ⟨v, hv⟩) (hcR ⟨v, hv⟩)
    refine (hi.image (fun _ _ _ _ h => Subtype.ext h)).mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hy.1, fun heq => hy.2 ((hc y).symm.trans (heq.trans (hc ⟨v, hv⟩)))⟩
  · exact hout v hv

/-- It suffices that only finitely many infinite-degree vertices have finitely
many infinite-degree neighbors. The other infinite-degree vertices form a core. -/
theorem exists_unfriendly_of_finite_exceptional_hubs [Countable V] (G : SimpleGraph V)
    (hB : {v : V | (G.neighborSet v).Infinite ∧
      (G.neighborSet v ∩ {w : V | (G.neighborSet w).Infinite}).Finite}.Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  classical
  let I : Set V := {v | (G.neighborSet v).Infinite}
  let B : Set V := {v | v ∈ I ∧ (G.neighborSet v ∩ I).Finite}
  refine exists_unfriendly_of_infinite_core G (I \ B) ?_ ?_
  · intro v hv
    have hN : (G.neighborSet v ∩ I).Infinite :=
      Set.not_finite.mp (fun hfin => hv.2 ⟨hv.1, hfin⟩)
    exact (hN.sdiff hB).mono (fun _ hw => ⟨hw.1.1, hw.1.2, hw.2⟩)
  · exact hB.subset (fun _ hv =>
      Classical.byContradiction (fun hn => hv.1 ⟨hv.2, hn⟩))

/-- The core hypothesis supplies every ordinal game clock in any universe. -/
theorem all_clocks_of_infinite_core [Countable V] (G : SimpleGraph V)
    (R : Set V) (hR : ∀ x ∈ R, (G.neighborSet x ∩ R).Infinite)
    (hOutside : {x : V | x ∉ R ∧ (G.neighborSet x).Infinite}.Finite) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α := by
  exact all_clocks_of_global G (exists_unfriendly_of_infinite_core G R hR hOutside)

/-- The finite-exception class satisfies Challenge 10 at every clock. -/
theorem all_clocks_of_finite_exceptional_hubs [Countable V] (G : SimpleGraph V)
    (hB : {x : V | (G.neighborSet x).Infinite ∧
      (G.neighborSet x ∩ {w : V | (G.neighborSet w).Infinite}).Finite}.Finite) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α := by
  exact all_clocks_of_global G (exists_unfriendly_of_finite_exceptional_hubs G hB)

end TenChallenges.Continuation

theorem solution {V : Type u} [Countable V] (G : SimpleGraph V)
    (R : Set V) (hR : ∀ x ∈ R, (G.neighborSet x ∩ R).Infinite)
    (hOutside : {x : V | x ∉ R ∧ (G.neighborSet x).Infinite}.Finite)
    (r : Ordinal.{v}) : PartitionerWins G (emptyPartition V) r :=
  TenChallenges.Continuation.all_clocks_of_infinite_core G R hR hOutside r

#print axioms solution
