-- Prove2me | solution 1 for TenChallenges.challenge_10_finiteCooccurrence
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T21:51:37.384124+00:00
-- url     : https://prove2.me/submissions/9d1135f7-1557-4fbc-bb6a-b66f627d88a3

import Definitions.Def_TenChallenges_Challenge_10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.Logic.Equiv.Finset
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
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

/- Inlined from Continuation/UnfriendlyRecurrentBlocks.lean. -/
/-!
# Recurrent finite blocks give robust colourings of infinite-degree vertices

A *piece* is a finite set of finite-degree vertices. If infinitely many pairwise
disjoint pieces have all their outside neighbours in a common finite set `A`
together with an already frozen set `D`, and each piece meets every vertex of `A`,
then `A` can be coloured so that every strongly maximal completion gives each
vertex of `A` an opposite-coloured neighbour in infinitely many of the pieces.

The witnesses are permanent: they depend only on the colours on `A ∪ D` and on
strong maximality, so they survive any later colouring of other vertices. Zorn's
lemma then assembles these blocks without any limit-stage loss.

This is a special case of the countable unfriendly partition problem. It does
not prove the unrestricted conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators

variable {V : Type u}

/-- Directed crossing count over a finite set of directed pairs. -/
def cutOn (E : Finset (V × V)) (c : V → Bool) : ℤ :=
  ∑ e ∈ E, cutIndicator c e

theorem cutIndicator_nonneg (c : V → Bool) (e : V × V) : 0 ≤ cutIndicator c e := by
  unfold cutIndicator
  split_ifs <;> omega

theorem cutIndicator_le_one (c : V → Bool) (e : V × V) : cutIndicator c e ≤ 1 := by
  unfold cutIndicator
  split_ifs <;> omega

theorem cutOn_le_card (E : Finset (V × V)) (c : V → Bool) : cutOn E c ≤ E.card := by
  have h := Finset.sum_le_card_nsmul E (cutIndicator c) 1
    (fun e _ => cutIndicator_le_one c e)
  simpa [cutOn] using h

/-- The crossing count depends only on the colours at endpoints of the listed pairs. -/
theorem cutOn_congr (E : Finset (V × V)) (c d : V → Bool)
    (h : ∀ e ∈ E, c e.1 = d e.1 ∧ c e.2 = d e.2) : cutOn E c = cutOn E d :=
  Finset.sum_congr rfl fun e he => by
    simp only [cutIndicator, (h e he).1, (h e he).2]

/-- The gain of a finite flip is the change of the crossing count on any finite set of
adjacent pairs containing all pairs incident with the flipped set. -/
theorem gain_eq_cutOn_sub (G : SimpleGraph V) (c : V → Bool) (S : Finset V)
    (E : Finset (V × V)) (hE : incident G S ⊆ (E : Set (V × V)))
    (hadj : ∀ e ∈ E, G.Adj e.1 e.2) :
    gain G c S = cutOn E (flip c S) - cutOn E c := by
  unfold gain cutOn
  rw [finsum_eq_sum_of_support_subset _ ((support_edgeDelta_flip_subset G c S).trans hE),
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e he => by simp only [edgeDelta, if_pos (hadj e he)]

open Classical in
/-- Recolouring an outside vertex that has no opponent inside the piece, but at least one
neighbour there, strictly increases the crossing count of the piece. -/
theorem cutOn_lt_cutOn_update (G : SimpleGraph V) (C : Finset V) (E : Finset (V × V))
    (hE : ∀ e ∈ E, G.Adj e.1 e.2 ∧ (e.1 ∈ C ∨ e.2 ∈ C))
    (c : V → Bool) (v : V) (hv : v ∉ C)
    (hsame : ∀ w ∈ C, G.Adj v w → c w = c v)
    (w : V) (hw : w ∈ C) (hvw : (v, w) ∈ E) :
    cutOn E c < cutOn E (Function.update c v (!c v)) := by
  refine Finset.sum_lt_sum (fun e he => ?_) ⟨(v, w), hvw, ?_⟩
  · obtain ⟨hadj, hC⟩ := hE e he
    by_cases h1 : e.1 = v
    · have h2 : e.2 ∈ C := hC.resolve_left (h1 ▸ hv)
      have h3 : c e.2 = c e.1 := h1 ▸ hsame e.2 h2 (h1 ▸ hadj)
      have h4 : cutIndicator c e = 0 := by simp [cutIndicator, h3]
      exact h4 ▸ cutIndicator_nonneg _ e
    · by_cases h2 : e.2 = v
      · have h3 : e.1 ∈ C := hC.resolve_right (h2 ▸ hv)
        have h4 : c e.1 = c e.2 := h2 ▸ hsame e.1 h3 (h2 ▸ hadj.symm)
        have h5 : cutIndicator c e = 0 := by simp [cutIndicator, h4]
        exact h5 ▸ cutIndicator_nonneg _ e
      · simp [cutIndicator, Function.update_of_ne h1, Function.update_of_ne h2]
  · have hwv : w ≠ v := fun h => hv (h ▸ hw)
    have hcw : c w = c v := hsame w hw (hE _ hvw).1
    simp [cutIndicator, Function.update_of_ne hwv, hcw]

/-- **Block selection.** Infinitely many pairwise disjoint finite pieces of finite-degree
vertices have all outside neighbours in `A ∪ D`, and every piece meets every vertex of the
finite set `A`. Then the colours on `A` can be chosen (keeping `p` elsewhere) so that every
strongly maximal colouring agreeing with the choice on `A ∪ D` gives each vertex of `A`
infinitely many opposite-coloured neighbours. -/
theorem exists_block_assignment (G : SimpleGraph V) (p : V → Bool) (A : Finset V) (D : Set V)
    {ι : Type*} [Infinite ι] (C : ι → Finset V)
    (hdisj : Pairwise (Function.onFun Disjoint C))
    (hfin : ∀ i, ∀ x ∈ C i, (G.neighborSet x).Finite)
    (hbdry : ∀ i, ∀ x ∈ C i, ∀ y, G.Adj x y → y ∈ C i ∨ y ∈ A ∨ y ∈ D)
    (hA : ∀ i, ∀ v ∈ A, v ∉ C i)
    (htouch : ∀ i, ∀ v ∈ A, ∃ x ∈ C i, G.Adj v x) :
    ∃ q : V → Bool, (∀ y, y ∉ A → q y = p y) ∧
      ∀ (M : Set V) (c : V → Bool), (∀ i, (C i : Set V) ⊆ M) → StrongMaximal G M c →
        (∀ y, y ∈ A ∨ y ∈ D → c y = q y) → ∀ v ∈ A, (oppositeSet G c v).Infinite := by
  classical
  let E : ι → Finset (V × V) := fun i => (incident_finite G (C i) (hfin i)).toFinset
  have hEmem : ∀ i e, e ∈ E i ↔ G.Adj e.1 e.2 ∧ (e.1 ∈ C i ∨ e.2 ∈ C i) := fun i e =>
    (incident_finite G (C i) (hfin i)).mem_toFinset
  have hend : ∀ i, ∀ e ∈ E i,
      (e.1 ∈ C i ∨ e.1 ∈ A ∨ e.1 ∈ D) ∧ (e.2 ∈ C i ∨ e.2 ∈ A ∨ e.2 ∈ D) := by
    intro i e he
    obtain ⟨hadj, h1 | h2⟩ := (hEmem i e).mp he
    · exact ⟨Or.inl h1, hbdry i e.1 h1 e.2 hadj⟩
    · exact ⟨hbdry i e.2 h2 e.1 hadj.symm, Or.inl h2⟩
  let K : ι → (V → Bool) → Prop := fun i d => ∀ y, y ∉ C i → y ∉ A → d y = p y
  have hmax : ∀ i, ∃ d, K i d ∧ ∀ d', K i d' → cutOn (E i) d' ≤ cutOn (E i) d := by
    intro i
    obtain ⟨m, ⟨d, hd, hdm⟩, hm⟩ := Int.exists_greatest_of_bdd
      (P := fun z => ∃ d, K i d ∧ cutOn (E i) d = z)
      ⟨(E i).card, fun z ⟨d, _, hz⟩ => hz ▸ cutOn_le_card (E i) d⟩
      ⟨cutOn (E i) p, p, fun _ _ _ => rfl, rfl⟩
    exact ⟨d, hd, fun d' hd' => hdm ▸ hm _ ⟨d', hd', rfl⟩⟩
  choose dsel hdK hdmax using hmax
  obtain ⟨t, ht⟩ := Finite.exists_infinite_fiber (fun i (a : A) => dsel i a.1)
  let q : V → Bool := fun y => if hy : y ∈ A then t ⟨y, hy⟩ else p y
  refine ⟨q, fun y hy => dif_neg hy, ?_⟩
  intro M c hCM hc hcq v hvA
  have key : ∀ i, (fun (a : A) => dsel i a.1) = t → ∃ w ∈ C i, G.Adj v w ∧ c w ≠ c v := by
    intro i hfib
    by_contra hno
    have hsame : ∀ w ∈ C i, G.Adj v w → c w = c v := fun w hw hvw =>
      Classical.byContradiction fun hne => hno ⟨w, hw, hvw, hne⟩
    obtain ⟨w, hwC, hvw⟩ := htouch i v hvA
    -- outside the piece, `c` agrees with the selected maximiser on `A ∪ D`
    have hout : ∀ y, y ∉ C i → (y ∈ A ∨ y ∈ D) → c y = dsel i y := by
      intro y hyC hy
      rw [hcq y hy]
      by_cases hyA : y ∈ A
      · exact (dif_pos hyA).trans (congrFun hfib ⟨y, hyA⟩).symm
      · exact (dif_neg hyA).trans (hdK i y hyC hyA).symm
    -- strong maximality: the interior of `c` is at least as good as the maximiser's interior
    let S : Finset V := (C i).filter fun y => dsel i y ≠ c y
    have hSC : S ⊆ C i := Finset.filter_subset _ _
    have hgain : gain G c S ≤ 0 := hc S (fun x hx => hCM i (hSC hx))
      (fun x hx => hfin i x (hSC hx))
    have hF1 : gain G c S = cutOn (E i) (flip c S) - cutOn (E i) c :=
      gain_eq_cutOn_sub G c S (E i)
        (fun e he => (hEmem i e).mpr ⟨he.1, he.2.imp (fun h => hSC h) (fun h => hSC h)⟩)
        (fun e he => ((hEmem i e).mp he).1)
    have hflip : ∀ y, (y ∈ C i ∨ y ∈ A ∨ y ∈ D) → flip c S y = dsel i y := by
      intro y hy
      by_cases hyC : y ∈ C i
      · by_cases hyd : dsel i y = c y
        · have hyS : y ∉ S := fun h => (Finset.mem_filter.mp h).2 hyd
          exact (if_neg hyS).trans hyd.symm
        · have hyS : y ∈ S := Finset.mem_filter.mpr ⟨hyC, hyd⟩
          refine (if_pos hyS).trans ?_
          revert hyd
          cases dsel i y <;> cases c y <;> simp
      · have hyS : y ∉ S := fun h => hyC (hSC h)
        exact (if_neg hyS).trans (hout y hyC (hy.resolve_left hyC))
    have h1 : cutOn (E i) (flip c S) = cutOn (E i) (dsel i) :=
      cutOn_congr _ _ _ fun e he => ⟨hflip e.1 (hend i e he).1, hflip e.2 (hend i e he).2⟩
    -- recolouring `v` strictly improves the piece
    have hlt : cutOn (E i) c < cutOn (E i) (Function.update c v (!c v)) :=
      cutOn_lt_cutOn_update G (C i) (E i) (fun e he => (hEmem i e).mp he) c v (hA i v hvA)
        hsame w hwC ((hEmem i (v, w)).mpr ⟨hvw, Or.inr hwC⟩)
    -- but the recoloured state is admissible for the maximisation
    let d' : V → Bool := fun y =>
      if y ∈ C i ∨ y ∈ A then Function.update c v (!c v) y else p y
    have hd'K : K i d' := fun y hyC hyA => if_neg (fun h => h.elim hyC hyA)
    have h2 : cutOn (E i) (Function.update c v (!c v)) = cutOn (E i) d' := by
      have hpt : ∀ y, (y ∈ C i ∨ y ∈ A ∨ y ∈ D) → Function.update c v (!c v) y = d' y := by
        intro y hy
        by_cases hyCA : y ∈ C i ∨ y ∈ A
        · exact (if_pos hyCA).symm
        · have hyC : y ∉ C i := fun h => hyCA (Or.inl h)
          have hyA : y ∉ A := fun h => hyCA (Or.inr h)
          have hyD : y ∈ D := (hy.resolve_left hyC).resolve_left hyA
          have hyv : y ≠ v := fun h => hyA (h ▸ hvA)
          rw [Function.update_of_ne hyv, hcq y (Or.inr hyD)]
          exact (dif_neg hyA).trans (if_neg hyCA).symm
      exact cutOn_congr _ _ _ fun e he => ⟨hpt e.1 (hend i e he).1, hpt e.2 (hend i e he).2⟩
    have h3 := hdmax i d' hd'K
    omega
  haveI : Infinite ((fun i (a : A) => dsel i a.1) ⁻¹' {t}) := ht
  choose w hwC hvw hne using key
  refine Set.infinite_of_injective_forall_mem
    (f := fun i : ((fun i (a : A) => dsel i a.1) ⁻¹' {t}) => w i.1 i.2) ?_ ?_
  · intro i j hij
    by_contra hne'
    have hd : Disjoint (C i.1) (C j.1) := hdisj fun h => hne' (Subtype.ext h)
    have hij' : w i.1 i.2 = w j.1 j.2 := hij
    have hj : w i.1 i.2 ∈ C j.1 := hij' ▸ hwC j.1 j.2
    exact Finset.disjoint_left.mp hd (hwC i.1 i.2) hj
  · intro i
    exact ⟨hvw i.1 i.2, hne i.1 i.2⟩

/-- A colouring `q`, frozen on `S`, is *robust* for strong maximality on `M` if every
colouring that is strongly maximal on `M` and agrees with `q` on `S` gives each vertex of
`S` infinitely many opposite-coloured neighbours. The property is closed under unions of
chains, since it quantifies over all strongly maximal completions. -/
def Robust (G : SimpleGraph V) (M S : Set V) (q : V → Bool) : Prop :=
  ∀ c : V → Bool, StrongMaximal G M c → Set.EqOn c q S →
    ∀ v ∈ S, (oppositeSet G c v).Infinite

/-- `A` is a *recurrent block over* `S`: infinitely many pairwise disjoint finite pieces of
finite-degree vertices have all their outside neighbours in `A ∪ S`, and each piece meets
every vertex of `A`. When `A ∪ S` consists of infinite-degree vertices, a piece is a finite
union of components of the graph induced on the finite-degree vertices, and the condition
says that the part of its boundary outside `S` is exactly `A`. -/
def RecurrentBlock (G : SimpleGraph V) (S : Set V) (A : Finset V) : Prop :=
  ∃ C : ℕ → Finset V, Pairwise (Function.onFun Disjoint C) ∧
    (∀ i, ∀ x ∈ C i, (G.neighborSet x).Finite) ∧
    (∀ i, ∀ x ∈ C i, ∀ y, G.Adj x y → y ∈ C i ∨ y ∈ A ∨ y ∈ S) ∧
    (∀ i, ∀ v ∈ A, ∃ x ∈ C i, G.Adj v x)

/-- A robust frozen colouring extends across a recurrent block of infinite-degree vertices. -/
theorem Robust.extend_block (G : SimpleGraph V) (M S : Set V) (q : V → Bool)
    (hq : Robust G M S q) (A : Finset V) (hAS : ∀ v ∈ A, v ∉ S)
    (hAinf : ∀ v ∈ A, (G.neighborSet v).Infinite)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M)
    (hblock : RecurrentBlock G S A) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M (S ∪ (A : Set V)) q' := by
  obtain ⟨C, hdisj, hfin, hbdry, htouch⟩ := hblock
  obtain ⟨q', hq'p, hq'⟩ := exists_block_assignment G q A S C hdisj hfin hbdry
    (fun i v hv hvC => hAinf v hv (hfin i v hvC)) htouch
  have hq'S : Set.EqOn q' q S := fun y hy => hq'p y (fun hyA => hAS y hyA hy)
  refine ⟨q', hq'S, ?_⟩
  intro c hc hcq v hv
  rcases hv with hvS | hvA
  · exact hq c hc (fun y hy => (hcq (Or.inl hy)).trans (hq'S hy)) v hvS
  · exact hq' M c (fun i x hx => hM x (hfin i x hx)) hc
      (fun y hy => hcq (hy.elim (fun h => Or.inr h) (fun h => Or.inl h))) v hvA

/-- Maximal robust frozen colourings exist inside any target set `H`. No countability,
enumeration, or limit-stage argument is needed. -/
theorem exists_maximal_robust (G : SimpleGraph V) (M H : Set V) :
    ∃ (S : Set V) (q : V → Bool), S ⊆ H ∧ Robust G M S q ∧
      ∀ (S' : Set V) (q' : V → Bool), S' ⊆ H → Robust G M S' q' → S ⊆ S' →
        Set.EqOn q' q S → S' ⊆ S := by
  classical
  let T : Type u := {P : Set V × (V → Bool) // P.1 ⊆ H ∧ Robust G M P.1 P.2}
  let r : T → T → Prop := fun P Q => P.1.1 ⊆ Q.1.1 ∧ Set.EqOn Q.1.2 P.1.2 P.1.1
  have htrans : ∀ {a b c : T}, r a b → r b c → r a c := fun {a b c} hab hbc =>
    ⟨hab.1.trans hbc.1, fun y hy => (hbc.2 (hab.1 hy)).trans (hab.2 hy)⟩
  have hchain : ∀ c : Set T, IsChain r c → ∃ ub, ∀ a ∈ c, r a ub := by
    intro c hc
    let dom : Set V := ⋃ P ∈ c, P.1.1
    let col : V → Bool := fun y =>
      if h : ∃ P ∈ c, y ∈ P.1.1 then (Classical.choose h).1.2 y else false
    have hcol : ∀ P ∈ c, Set.EqOn col P.1.2 P.1.1 := by
      intro P hP y hy
      have h : ∃ P ∈ c, y ∈ P.1.1 := ⟨P, hP, hy⟩
      have hspec := Classical.choose_spec h
      have hval : col y = (Classical.choose h).1.2 y := dif_pos h
      rw [hval]
      by_cases hPQ : Classical.choose h = P
      · rw [hPQ]
      · rcases hc hspec.1 hP hPQ with hle | hle
        · exact (hle.2 hspec.2).symm
        · exact hle.2 hy
    have hdomH : dom ⊆ H := Set.iUnion₂_subset fun P _ => P.2.1
    have hrob : Robust G M dom col := by
      intro cc hcc heq v hv
      obtain ⟨P, hP, hvP⟩ := Set.mem_iUnion₂.mp hv
      exact P.2.2 cc hcc
        (fun y hy => (heq (Set.mem_iUnion₂.mpr ⟨P, hP, hy⟩)).trans (hcol P hP hy)) v hvP
    exact ⟨⟨(dom, col), hdomH, hrob⟩, fun P hP =>
      ⟨fun y hy => Set.mem_iUnion₂.mpr ⟨P, hP, hy⟩, hcol P hP⟩⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hchain htrans
  refine ⟨m.1.1, m.1.2, m.2.1, m.2.2, fun S' q' hS'H hrob hSS' heq => ?_⟩
  exact (hm ⟨(S', q'), hS'H, hrob⟩ ⟨hSS', heq⟩).1

/-- **Relative recurrence.** Suppose that every proper subset `S` of the infinite-degree
vertices admits a nonempty recurrent block of further infinite-degree vertices. Then the
infinite-degree vertices have a robust colouring: every colouring extending it that is
strongly maximal on the finite-degree vertices gives every infinite-degree vertex
infinitely many opposite-coloured neighbours. -/
theorem exists_robust_of_recurrent_blocks (G : SimpleGraph V)
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      S ≠ {v | (G.neighborSet v).Infinite} →
      ∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) :
    ∃ q : V → Bool, Robust G {v | (G.neighborSet v).Infinite}ᶜ
      {v | (G.neighborSet v).Infinite} q := by
  obtain ⟨S, q, hSH, hrob, hmax⟩ := exists_maximal_robust G
    {v | (G.neighborSet v).Infinite}ᶜ {v | (G.neighborSet v).Infinite}
  by_cases hS : S = {v | (G.neighborSet v).Infinite}
  · exact ⟨q, hS ▸ hrob⟩
  · obtain ⟨A, ⟨a, ha⟩, hA, hblock⟩ := h S hSH hS
    obtain ⟨q', hq'q, hq'⟩ := Robust.extend_block G _ S q hrob A (fun v hv => (hA v hv).2)
      (fun v hv => (hA v hv).1) (fun x hx hinf => hinf hx) hblock
    have hsub : S ∪ (A : Set V) ⊆ S := hmax (S ∪ (A : Set V)) q'
      (Set.union_subset hSH (fun v hv => (hA v hv).1)) hq' Set.subset_union_left hq'q
    exact ((hA a ha).2 (hsub (Or.inr ha))).elim

/-- A countable graph has an unfriendly partition whenever every proper subset of its
infinite-degree vertices admits a nonempty recurrent block of further such vertices. -/
theorem exists_unfriendly_of_recurrent_blocks [Countable V] (G : SimpleGraph V)
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      S ≠ {v | (G.neighborSet v).Infinite} →
      ∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  obtain ⟨q, hq⟩ := exists_robust_of_recurrent_blocks G h
  obtain ⟨c, hcq, hc⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
    {v | (G.neighborSet v).Infinite} q
  refine ⟨fun v => some (c v), fun v => ?_⟩
  exact (Classical.em (G.neighborSet v).Finite).elim
    (fun hN => unfriendlyAt_of_strongMaximal G _ c hc v (fun hInf => hInf hN) hN)
    (fun hN => unfriendly_of_infinite_opposite G c v (hq c hc hcq v (Set.not_finite.mp hN)))

/-- **Recurrent full boundaries.** If every infinite-degree vertex lies in a finite set `B`
of infinite-degree vertices that is the exact outside neighbourhood of infinitely many
pairwise disjoint finite pieces of finite-degree vertices, then the countable graph has
an unfriendly partition. Different boundaries may overlap arbitrarily. -/
theorem exists_unfriendly_of_recurrent_boundaries [Countable V] (G : SimpleGraph V)
    (h : ∀ v, (G.neighborSet v).Infinite →
      ∃ B : Finset V, v ∈ B ∧ (∀ u ∈ B, (G.neighborSet u).Infinite) ∧
        RecurrentBlock G ∅ B) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  classical
  refine exists_unfriendly_of_recurrent_blocks G fun S hSH hS => ?_
  obtain ⟨v, hvI, hvS⟩ : ∃ v, (G.neighborSet v).Infinite ∧ v ∉ S := by
    by_contra hno
    exact hS (Set.Subset.antisymm hSH fun v hv =>
      Classical.byContradiction fun hvS => hno ⟨v, hv, hvS⟩)
  obtain ⟨B, hvB, hBI, C, hdisj, hfin, hbdry, htouch⟩ := h v hvI
  refine ⟨B.filter (· ∉ S), ⟨v, Finset.mem_filter.mpr ⟨hvB, hvS⟩⟩,
    fun u hu => ⟨hBI u (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩,
    C, hdisj, hfin, ?_, fun i u hu => htouch i u (Finset.mem_filter.mp hu).1⟩
  intro i x hx y hxy
  rcases hbdry i x hx y hxy with hC | hB | hE
  · exact Or.inl hC
  · by_cases hyS : y ∈ S
    · exact Or.inr (Or.inr hyS)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hB, hyS⟩))
  · exact hE.elim

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyPairProfile.lean. -/
/-!
# Universal opponent certificates for pair profiles

The matrix stores twice the undirected interaction coefficient. Both matrix
orientations are summed, so the representation is for four times the profile.
No bound on the finite boundary size is used in the certificate.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PairProfile

open scoped BigOperators

variable {B : Type u} [Fintype B]

def quadratic (a : B → B → ℤ) (b : B → Bool) : ℤ :=
  ∑ u, ∑ v, if b u ≠ b v then a u v else 0

open Classical in
noncomputable def toggle (b : B → Bool) (v : B) : B → Bool :=
  Function.update b v (!b v)

def row (a : B → B → ℤ) (b : B → Bool) (v : B) : ℤ :=
  ∑ u, if b v ≠ b u then a v u else -a v u

def weight (a : B → B → ℤ) (v : B) : ℤ := ∑ u, |a v u|

def Favoured (a : ℤ) (x y : Bool) : Prop :=
  (0 < a ∧ x ≠ y) ∨ (a < 0 ∧ x = y)

open Classical in
noncomputable def favouredWeight (a : B → B → ℤ) (b : B → Bool) (v : B) : ℤ :=
  ∑ u, if Favoured (a v u) (b v) (b u) then |a v u| else 0

def Represents (Q : (B → Bool) → ℤ) (K : ℤ) (a : B → B → ℤ) : Prop :=
  (∀ u v, a u v = a v u) ∧ (∀ v, a v v = 0) ∧
    ∀ b, 4 * Q b = K + quadratic a b

omit [Fintype B] in
open Classical in
private theorem term_toggle (a : B → B → ℤ) (hdiag : ∀ v, a v v = 0)
    (b : B → Bool) (v u w : B) :
    (if b u ≠ b w then a u w else 0) -
        (if toggle b v u ≠ toggle b v w then a u w else 0) =
      (if u = v then (if b v ≠ b w then a v w else -a v w) else 0) +
      (if w = v then (if b u ≠ b v then a u v else -a u v) else 0) := by
  classical
  by_cases hu : u = v <;> by_cases hw : w = v
  all_goals cases hv : b v <;> cases hbu : b u <;> cases hbw : b w
  all_goals simp_all [toggle]

private theorem quadratic_difference (a : B → B → ℤ)
    (hsym : ∀ u v, a u v = a v u) (hdiag : ∀ v, a v v = 0)
    (b : B → Bool) (v : B) :
    quadratic a b - quadratic a (toggle b v) = 2 * row a b v := by
  classical
  unfold quadratic
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, term_toggle a hdiag b v]
  simp_rw [Finset.sum_add_distrib]
  have hA : (∑ u, ∑ w,
      if u = v then (if b v ≠ b w then a v w else -a v w) else 0) = row a b v := by
    simp [Finset.sum_ite_irrel, row]
  rw [hA]
  simp [row, hsym, ne_comm, two_mul]

theorem profile_difference (Q : (B → Bool) → ℤ) (K : ℤ) (a : B → B → ℤ)
    (hrep : Represents Q K a) (b : B → Bool) (v : B) :
    2 * (Q b - Q (toggle b v)) = row a b v := by
  have h := quadratic_difference a hrep.1 hrep.2.1 b v
  have h₁ := hrep.2.2 b
  have h₂ := hrep.2.2 (toggle b v)
  omega

private theorem row_star (a : B → B → ℤ) (hdiag : ∀ v, a v v = 0) (v : B) :
    row a (fun u => decide (0 < a v u)) v = weight a v := by
  classical
  unfold row weight
  simp only [hdiag, lt_self_iff_false, decide_false]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases ha : 0 < a v u
  · simp [ha, abs_of_pos ha]
  · simp [ha, abs_of_nonpos (le_of_not_gt ha)]

open Classical in
private theorem signed_term (a : ℤ) (x y : Bool) :
    (if x ≠ y then a else -a) =
      2 * (if Favoured a x y then |a| else 0) - |a| := by
  rcases lt_trichotomy a 0 with hn | rfl | hp
  · cases x <;> cases y <;> simp [Favoured, hn, not_lt_of_ge hn.le, abs_of_neg hn, two_mul]
  · cases x <;> cases y <;> simp [Favoured]
  · cases x <;> cases y <;> simp [Favoured, hp, not_lt_of_ge hp.le, abs_of_pos hp, two_mul]

private theorem row_favoured (a : B → B → ℤ) (b : B → Bool) (v : B) :
    row a b v = 2 * favouredWeight a b v - weight a v := by
  classical
  unfold row favouredWeight weight
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun u _ => signed_term (a v u) (b v) (b u)

theorem weight_budget (Q : (B → Bool) → ℤ) (K : ℤ) (a : B → B → ℤ)
    (hrep : Represents Q K a) (d : B → ℤ)
    (hflip : ∀ b v, Q b - Q (toggle b v) ≤ d v) (v : B) :
    weight a v ≤ 2 * d v := by
  have h := profile_difference Q K a hrep (fun u => decide (0 < a v u)) v
  rw [row_star a hrep.2.1 v] at h
  linarith [hflip (fun u => decide (0 < a v u)) v]

/-- The integer-scaled universal opponent certificate. The response inequality
holds separately for every maximizing completion, so the conclusion does too. -/
theorem universal_opponent_certificate (Q : (B → Bool) → ℤ) (K : ℤ)
    (a : B → B → ℤ) (hrep : Represents Q K a) (d : B → ℤ)
    (hflip : ∀ b v, Q b - Q (toggle b v) ≤ d v)
    (b : B → Bool) (v : B) (o : ℤ)
    (hresponse : d v + Q b - Q (toggle b v) ≤ 2 * o) :
    weight a v ≤ 2 * d v ∧
      2 * d v - weight a v + 2 * favouredWeight a b v ≤ 4 * o := by
  refine ⟨weight_budget Q K a hrep d hflip v, ?_⟩
  have hdiff := profile_difference Q K a hrep b v
  have hrow := row_favoured a b v
  linarith

end TenChallenges.Continuation.PairProfile

/- Inlined from Continuation/UnfriendlyPairRepresentation.lean. -/
/-!
# Complement-invariant profiles on boundaries of size at most three

The coefficients are integers representing twice the undirected interaction
weight. This file provides pair representations for every even integer profile
on a finite boundary with at most three vertices.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PairProfile

open scoped BigOperators

private theorem vec_one_eta (b : Fin 1 → Bool) : ![b 0] = b := by
  funext i
  fin_cases i
  rfl

private theorem vec_two_eta (b : Fin 2 → Bool) : ![b 0, b 1] = b := by
  funext i
  fin_cases i <;> rfl

private theorem vec_three_eta (b : Fin 3 → Bool) : ![b 0, b 1, b 2] = b := by
  funext i
  fin_cases i <;> rfl

private theorem quadratic_two (p : ℤ) (b : Fin 2 → Bool) :
    quadratic ![![0, p], ![p, 0]] b = 2 * (if b 0 ≠ b 1 then p else 0) := by
  cases h₀ : b 0 <;> cases h₁ : b 1
  all_goals simp [quadratic, Fin.sum_univ_succ, h₀, h₁, two_mul]

private theorem quadratic_three (p q r : ℤ) (b : Fin 3 → Bool) :
    quadratic ![![0, p, q], ![p, 0, r], ![q, r, 0]] b =
      2 * (if b 0 ≠ b 1 then p else 0) +
      2 * (if b 0 ≠ b 2 then q else 0) +
      2 * (if b 1 ≠ b 2 then r else 0) := by
  cases h₀ : b 0 <;> cases h₁ : b 1 <;> cases h₂ : b 2
  all_goals simp [quadratic, Fin.sum_univ_succ, h₀, h₁, h₂, two_mul,
    add_left_comm, add_comm]

private def triple01 (f : Bool → Bool → Bool → ℤ) : ℤ :=
  f true false false + f false true false - f false false true - f false false false

private def triple02 (f : Bool → Bool → Bool → ℤ) : ℤ :=
  f true false false + f false false true - f false true false - f false false false

private def triple12 (f : Bool → Bool → Bool → ℤ) : ℤ :=
  f false true false + f false false true - f true false false - f false false false

private theorem even_three_identity (f : Bool → Bool → Bool → ℤ)
    (heven : ∀ x y z, f (!x) (!y) (!z) = f x y z) (x y z : Bool) :
    2 * f x y z = 2 * f false false false +
      (if x ≠ y then triple01 f else 0) +
      (if x ≠ z then triple02 f else 0) +
      (if y ≠ z then triple12 f else 0) := by
  simp only [Bool.forall_bool, Bool.not_true, Bool.not_false] at heven
  cases x <;> cases y <;> cases z
  all_goals simp only [triple01, triple02, triple12, ne_eq,
    Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false,
    ite_true, ite_false]
  all_goals omega

private theorem even_two_identity (f : Bool → Bool → ℤ)
    (heven : ∀ x y, f (!x) (!y) = f x y) (x y : Bool) :
    2 * f x y = 2 * f false false +
      (if x ≠ y then 2 * (f false true - f false false) else 0) := by
  simp only [Bool.forall_bool, Bool.not_true, Bool.not_false] at heven
  cases x <;> cases y
  all_goals simp only [ne_eq, Bool.false_eq_true, Bool.true_eq_false,
    not_false_eq_true, not_true_eq_false, ite_true, ite_false]
  all_goals omega

private theorem represents_zero (Q : (Fin 0 → Bool) → ℤ) :
    ∃ K a, Represents Q K a := by
  refine ⟨4 * Q ![], fun _ _ => 0, fun _ _ => rfl, fun _ => rfl, fun b => ?_⟩
  have hb : b = ![] := Subsingleton.elim _ _
  simp [quadratic, hb]

private theorem represents_one (Q : (Fin 1 → Bool) → ℤ)
    (heven : ∀ b, Q (fun i => !b i) = Q b) :
    ∃ K a, Represents Q K a := by
  have hf : Q ![true] = Q ![false] :=
    (congrArg Q (vec_one_eta (fun i => !(![false] i)))).trans (heven ![false])
  refine ⟨4 * Q ![false], fun _ _ => 0, fun _ _ => rfl, fun _ => rfl, fun b => ?_⟩
  have hQ : Q b = Q ![false] := by
    rw [← vec_one_eta b]
    cases b 0
    · rfl
    · exact hf
  simp [quadratic, hQ]

private theorem represents_two (Q : (Fin 2 → Bool) → ℤ)
    (heven : ∀ b, Q (fun i => !b i) = Q b) :
    ∃ K a, Represents Q K a := by
  let f : Bool → Bool → ℤ := fun x y => Q ![x, y]
  have hf : ∀ x y, f (!x) (!y) = f x y := fun x y =>
    (congrArg Q (vec_two_eta (fun i => !(![x, y] i)))).trans (heven ![x, y])
  let t : ℤ := 2 * (f false true - f false false)
  refine ⟨4 * f false false, ![![0, t], ![t, 0]], ?_, ?_, ?_⟩
  · intro u v
    fin_cases u <;> fin_cases v <;> rfl
  · intro v
    fin_cases v <;> rfl
  · intro b
    have h := even_two_identity f hf (b 0) (b 1)
    have hQ : Q b = f (b 0) (b 1) := (congrArg Q (vec_two_eta b)).symm
    rw [hQ, quadratic_two]
    dsimp only [t]
    omega

private theorem represents_three (Q : (Fin 3 → Bool) → ℤ)
    (heven : ∀ b, Q (fun i => !b i) = Q b) :
    ∃ K a, Represents Q K a := by
  let f : Bool → Bool → Bool → ℤ := fun x y z => Q ![x, y, z]
  have hf : ∀ x y z, f (!x) (!y) (!z) = f x y z := fun x y z =>
    (congrArg Q (vec_three_eta (fun i => !(![x, y, z] i)))).trans (heven ![x, y, z])
  let a : Fin 3 → Fin 3 → ℤ :=
    ![![0, triple01 f, triple02 f], ![triple01 f, 0, triple12 f],
      ![triple02 f, triple12 f, 0]]
  refine ⟨4 * f false false false, a, ?_, ?_, ?_⟩
  · intro u v
    fin_cases u <;> fin_cases v <;> rfl
  · intro v
    fin_cases v <;> rfl
  · intro b
    have h := even_three_identity f hf (b 0) (b 1) (b 2)
    have hQ : Q b = f (b 0) (b 1) (b 2) := (congrArg Q (vec_three_eta b)).symm
    rw [hQ, quadratic_three]
    omega

private theorem represents_fin (n : ℕ) (hn : n ≤ 3)
    (Q : (Fin n → Bool) → ℤ) (heven : ∀ b, Q (fun i => !b i) = Q b) :
    ∃ K a, Represents Q K a := by
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn' with rfl | rfl | rfl | rfl
  · exact represents_zero Q
  · exact represents_one Q heven
  · exact represents_two Q heven
  · exact represents_three Q heven

/-- Every complement-invariant integer profile on at most three boundary
vertices has a constant-plus-pair representation, with integer-scaled weights. -/
theorem exists_representation_of_card_le_three {B : Type u} [Fintype B]
    (hB : Fintype.card B ≤ 3) (Q : (B → Bool) → ℤ)
    (heven : ∀ b, Q (fun i => !b i) = Q b) :
    ∃ K a, Represents Q K a := by
  classical
  let e := Fintype.equivFin B
  let Q' : (Fin (Fintype.card B) → Bool) → ℤ := fun b => Q (fun v => b (e v))
  have heven' : ∀ b, Q' (fun i => !b i) = Q' b :=
    fun b => heven (fun v => b (e v))
  obtain ⟨K, a, hrep⟩ := represents_fin (Fintype.card B) hB Q' heven'
  refine ⟨K, fun u v => a (e u) (e v), fun u v => hrep.1 (e u) (e v),
    fun v => hrep.2.1 (e v), fun b => ?_⟩
  have h := hrep.2.2 (fun i => b (e.symm i))
  simp only [quadratic] at h ⊢
  simpa only [← e.sum_comp, e.symm_apply_apply, Q'] using h

end TenChallenges.Continuation.PairProfile

/- Inlined from Continuation/UnfriendlyComponentProfile.lean. -/
/-!
# Full-boundary profiles of finite pieces

Scores and incidence counts include both orientations, as in `Energy.gain`.
This common factor of two preserves all opponent-positivity certificates.
The full outside boundary is fixed before any colours on hubs are prescribed.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

open scoped BigOperators

variable {V : Type u}

open Classical in
noncomputable def pieceDegree (E : Finset (V × V)) (v : V) : ℤ :=
  ∑ e ∈ E, if e.1 = v ∨ e.2 = v then 1 else 0

open Classical in
noncomputable def pieceOpponents (E : Finset (V × V)) (c : V → Bool) (v : V) : ℤ :=
  ∑ e ∈ E, if e.1 = v ∨ e.2 = v then cutIndicator c e else 0

theorem pieceOpponents_nonneg (E : Finset (V × V)) (c : V → Bool) (v : V) :
    0 ≤ pieceOpponents E c v := by
  classical
  apply Finset.sum_nonneg
  intro e he
  split_ifs
  · exact cutIndicator_nonneg c e
  · exact le_rfl

theorem pieceOpponents_le_degree (E : Finset (V × V)) (c : V → Bool) (v : V) :
    pieceOpponents E c v ≤ pieceDegree E v := by
  classical
  apply Finset.sum_le_sum
  intro e he
  split_ifs
  · exact cutIndicator_le_one c e
  · exact le_rfl

open Classical in
private theorem cutIndicator_update_boundary (c : V → Bool) (v : V) (e : V × V)
    (hne : e.1 ≠ e.2) :
    cutIndicator (Function.update c v (!c v)) e =
      cutIndicator c e + (if e.1 = v ∨ e.2 = v then 1 else 0) -
        2 * (if e.1 = v ∨ e.2 = v then cutIndicator c e else 0) := by
  classical
  by_cases h₁ : e.1 = v <;> by_cases h₂ : e.2 = v
  all_goals cases hc₁ : c e.1 <;> cases hc₂ : c e.2 <;> cases hcv : c v
  all_goals simp_all [cutIndicator]

open Classical in
theorem cutOn_update_boundary (G : SimpleGraph V) (E : Finset (V × V))
    (hE : ∀ e ∈ E, G.Adj e.1 e.2) (c : V → Bool) (v : V) :
    cutOn E (Function.update c v (!c v)) =
      cutOn E c + pieceDegree E v - 2 * pieceOpponents E c v := by
  classical
  unfold cutOn pieceDegree pieceOpponents
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e he =>
    cutIndicator_update_boundary c v e (G.ne_of_adj (hE e he))

/-- A finite set of finite-degree vertices, with its full outside boundary. -/
structure FinitePiece (G : SimpleGraph V) where
  verts : Finset V
  finite_degree : ∀ x ∈ verts, (G.neighborSet x).Finite

namespace FinitePiece

variable {G : SimpleGraph V} (P : FinitePiece G)

noncomputable def edges : Finset (V × V) :=
  (incident_finite G P.verts P.finite_degree).toFinset

open Classical in
noncomputable def boundary : Finset V :=
  (P.edges.image Prod.fst ∪ P.edges.image Prod.snd).filter (· ∉ P.verts)

noncomputable def score (c : V → Bool) : ℤ := cutOn P.edges c

def Respects (b : P.boundary → Bool) (c : V → Bool) : Prop :=
  ∀ v : P.boundary, c v.val = b v

theorem edge_mem (e : V × V) :
    e ∈ P.edges ↔ G.Adj e.1 e.2 ∧ (e.1 ∈ P.verts ∨ e.2 ∈ P.verts) :=
  (incident_finite G P.verts P.finite_degree).mem_toFinset

theorem boundary_not_mem {v : V} (hv : v ∈ P.boundary) : v ∉ P.verts := by
  classical
  exact (Finset.mem_filter.mp hv).2

theorem endpoints {e : V × V} (he : e ∈ P.edges) :
    (e.1 ∈ P.verts ∨ e.1 ∈ P.boundary) ∧
      (e.2 ∈ P.verts ∨ e.2 ∈ P.boundary) := by
  classical
  exact ⟨if h : e.1 ∈ P.verts then Or.inl h else Or.inr
      (Finset.mem_filter.mpr ⟨Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨e, he, rfl⟩), h⟩),
    if h : e.2 ∈ P.verts then Or.inl h else Or.inr
      (Finset.mem_filter.mpr ⟨Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, he, rfl⟩), h⟩)⟩

private theorem exists_maximum (b : P.boundary → Bool) :
    ∃ c : V → Bool, P.Respects b c ∧
      ∀ d : V → Bool, P.Respects b d → P.score d ≤ P.score c := by
  classical
  let c₀ : V → Bool := fun x => if hx : x ∈ P.boundary then b ⟨x, hx⟩ else false
  have hc₀ : P.Respects b c₀ := fun v => dif_pos v.property
  obtain ⟨m, ⟨c, hc, hcm⟩, hm⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ c, P.Respects b c ∧ P.score c = z)
    ⟨P.edges.card, fun z ⟨c, _, hz⟩ => hz ▸ cutOn_le_card P.edges c⟩
    ⟨P.score c₀, c₀, hc₀, rfl⟩
  exact ⟨c, hc, fun d hd => hcm ▸ hm _ ⟨d, hd, rfl⟩⟩

noncomputable def profile (b : P.boundary → Bool) : ℤ :=
  P.score (Classical.choose (P.exists_maximum b))

theorem profile_attained (b : P.boundary → Bool) :
    ∃ c : V → Bool, P.Respects b c ∧ P.score c = P.profile b :=
  ⟨Classical.choose (P.exists_maximum b), (Classical.choose_spec (P.exists_maximum b)).1, rfl⟩

theorem le_profile (b : P.boundary → Bool) (c : V → Bool) (hc : P.Respects b c) :
    P.score c ≤ P.profile b :=
  (Classical.choose_spec (P.exists_maximum b)).2 c hc

private theorem score_not (c : V → Bool) : P.score (fun x => !c x) = P.score c := by
  unfold score cutOn
  refine Finset.sum_congr rfl fun e _ => ?_
  cases h₁ : c e.1 <;> cases h₂ : c e.2 <;> simp [cutIndicator, h₁, h₂]

theorem profile_even (b : P.boundary → Bool) :
    P.profile (fun v => !b v) = P.profile b := by
  have hle : ∀ b, P.profile b ≤ P.profile (fun v => !b v) := by
    intro b
    obtain ⟨c, hc, hmax⟩ := P.profile_attained b
    have hres : P.Respects (fun v => !b v) (fun x => !c x) :=
      fun v => congrArg Bool.not (hc v)
    have h := P.le_profile _ _ hres
    rw [P.score_not c] at h
    omega
  exact le_antisymm (by simpa only [Bool.not_not] using hle (fun v => !b v)) (hle b)

open Classical in
private theorem respects_update (b : P.boundary → Bool) (c : V → Bool)
    (hc : P.Respects b c) (v : P.boundary) :
    P.Respects (PairProfile.toggle b v) (Function.update c v.val (!c v.val)) := by
  classical
  intro w
  by_cases hw : w = v
  · subst w
    simpa only [PairProfile.toggle, Function.update_self] using congrArg Bool.not (hc v)
  · have hval : w.val ≠ v.val := fun h => hw (Subtype.ext h)
    simpa only [PairProfile.toggle, Function.update, dif_neg hval, dif_neg hw] using hc w

theorem profile_response (b : P.boundary → Bool) (c : V → Bool)
    (hc : P.Respects b c) (hmax : P.score c = P.profile b) (v : P.boundary) :
    pieceDegree P.edges v.val + P.profile b - P.profile (PairProfile.toggle b v) ≤
      2 * pieceOpponents P.edges c v.val := by
  classical
  have h := P.le_profile _ _ (P.respects_update b c hc v)
  have heq := cutOn_update_boundary G P.edges
    (fun e he => ((P.edge_mem e).mp he).1) c v.val
  change cutOn P.edges (Function.update c v.val (!c v.val)) ≤
    P.profile (PairProfile.toggle b v) at h
  rw [heq] at h
  change P.score c + pieceDegree P.edges v.val -
    2 * pieceOpponents P.edges c v.val ≤ P.profile (PairProfile.toggle b v) at h
  omega

theorem profile_flip_bound (b : P.boundary → Bool) (v : P.boundary) :
    P.profile b - P.profile (PairProfile.toggle b v) ≤ pieceDegree P.edges v.val := by
  obtain ⟨c, hc, hmax⟩ := P.profile_attained b
  have h := P.profile_response b c hc hmax v
  linarith [pieceOpponents_le_degree P.edges c v.val]

theorem eq_profile_of_strongMaximal (M : Set V) (c : V → Bool)
    (hPM : (P.verts : Set V) ⊆ M) (hc : StrongMaximal G M c)
    (b : P.boundary → Bool) (hcb : P.Respects b c) :
    P.score c = P.profile b := by
  classical
  obtain ⟨d, hd, hdmax⟩ := P.profile_attained b
  let S : Finset V := P.verts.filter (fun y => d y ≠ c y)
  have hSC : S ⊆ P.verts := Finset.filter_subset _ _
  have hgain := hc S (fun x hx => hPM (hSC hx))
    (fun x hx => P.finite_degree x (hSC hx))
  have hdiff : gain G c S = cutOn P.edges (flip c S) - cutOn P.edges c :=
    gain_eq_cutOn_sub G c S P.edges
      (fun e he => (P.edge_mem e).mpr
        ⟨he.1, he.2.imp (fun h => hSC h) (fun h => hSC h)⟩)
      (fun e he => ((P.edge_mem e).mp he).1)
  have hflip : ∀ y, y ∈ P.verts ∨ y ∈ P.boundary → flip c S y = d y := by
    intro y hy
    by_cases hyC : y ∈ P.verts
    · by_cases hyd : d y = c y
      · have hyS : y ∉ S := fun h => (Finset.mem_filter.mp h).2 hyd
        exact (if_neg hyS).trans hyd.symm
      · have hyS : y ∈ S := Finset.mem_filter.mpr ⟨hyC, hyd⟩
        refine (if_pos hyS).trans ?_
        revert hyd
        cases d y <;> cases c y <;> simp
    · have hyS : y ∉ S := fun h => hyC (hSC h)
      exact (if_neg hyS).trans
        ((hcb ⟨y, hy.resolve_left hyC⟩).trans (hd ⟨y, hy.resolve_left hyC⟩).symm)
  have hF : cutOn P.edges (flip c S) = P.score d :=
    cutOn_congr _ _ _ fun e he =>
      ⟨hflip e.1 (P.endpoints he).1, hflip e.2 (P.endpoints he).2⟩
  rw [hdiff, hF] at hgain
  change P.score d - P.score c ≤ 0 at hgain
  exact le_antisymm (P.le_profile b c hcb) (by omega)

/-- Strong maximality supplies the universal, completion-independent opponent certificate. -/
theorem opponent_certificate (M : Set V) (c : V → Bool)
    (hPM : (P.verts : Set V) ⊆ M) (hc : StrongMaximal G M c)
    (b : P.boundary → Bool) (hcb : P.Respects b c)
    (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (v : P.boundary) :
    PairProfile.weight a v ≤ 2 * pieceDegree P.edges v.val ∧
      2 * pieceDegree P.edges v.val - PairProfile.weight a v +
        2 * PairProfile.favouredWeight a b v ≤ 4 * pieceOpponents P.edges c v.val := by
  exact PairProfile.universal_opponent_certificate P.profile K a hrep
    (fun v => pieceDegree P.edges v.val) P.profile_flip_bound b v
    (pieceOpponents P.edges c v.val)
    (P.profile_response b c hcb (P.eq_profile_of_strongMaximal M c hPM hc b hcb) v)

theorem exists_opponent_of_pos (c : V → Bool) (v : P.boundary)
    (hop : 0 < pieceOpponents P.edges c v.val) :
    ∃ w ∈ P.verts, G.Adj v.val w ∧ c w ≠ c v.val := by
  classical
  have hnon : ∀ e ∈ P.edges, 0 ≤
      (if e.1 = v.val ∨ e.2 = v.val then cutIndicator c e else 0) := by
    intro e he
    split_ifs
    · exact cutIndicator_nonneg c e
    · exact le_rfl
  obtain ⟨e, he, hpos⟩ := (Finset.sum_pos_iff_of_nonneg hnon).mp hop
  have hi : e.1 = v.val ∨ e.2 = v.val := by
    by_contra hn
    simp only [if_neg hn, lt_self_iff_false] at hpos
  have hpc : 0 < cutIndicator c e := by simpa only [if_pos hi] using hpos
  have hne : c e.1 ≠ c e.2 := by
    intro h
    have hz : cutIndicator c e = 0 := by simp [cutIndicator, h]
    omega
  obtain ⟨hadj, hC⟩ := (P.edge_mem e).mp he
  have hv : v.val ∉ P.verts := P.boundary_not_mem v.property
  rcases hi with hL | hR
  · exact ⟨e.2, hC.resolve_left (fun h => hv (hL ▸ h)), hL ▸ hadj, (hL ▸ hne).symm⟩
  · exact ⟨e.1, hC.resolve_right (fun h => hv (hR ▸ h)), hR ▸ hadj.symm, hR ▸ hne⟩

theorem exists_pair_representation (hB : P.boundary.card ≤ 3) :
    ∃ K a, PairProfile.Represents P.profile K a := by
  apply PairProfile.exists_representation_of_card_le_three _ P.profile P.profile_even
  simpa only [Fintype.card_coe] using hB

theorem boundary_touch (v : P.boundary) :
    ∃ w ∈ P.verts, G.Adj v.val w := by
  classical
  obtain ⟨hends, hv⟩ := Finset.mem_filter.mp v.property
  rcases Finset.mem_union.mp hends with hL | hR
  · obtain ⟨e, he, hval⟩ := Finset.mem_image.mp hL
    have h := (P.edge_mem e).mp he
    exact ⟨e.2, h.2.resolve_left (fun he => hv (hval ▸ he)), hval ▸ h.1⟩
  · obtain ⟨e, he, hval⟩ := Finset.mem_image.mp hR
    have h := (P.edge_mem e).mp he
    exact ⟨e.1, h.2.resolve_right (fun he => hv (hval ▸ he)), hval ▸ h.1.symm⟩

theorem degree_pos (v : P.boundary) : 0 < pieceDegree P.edges v.val := by
  classical
  obtain ⟨w, hw, hvw⟩ := P.boundary_touch v
  have he : (v.val, w) ∈ P.edges := (P.edge_mem _).mpr ⟨hvw, Or.inr hw⟩
  have hs := Finset.single_le_sum (s := P.edges)
    (f := fun e => if e.1 = v.val ∨ e.2 = v.val then (1 : ℤ) else 0)
    (fun e _ => by split_ifs <;> omega) he
  rw [if_pos (Or.inl rfl)] at hs
  change 1 ≤ pieceDegree P.edges v.val at hs
  omega

open Classical in
private theorem favoured_term_nonneg (a : ℤ) (x y : Bool) :
    0 ≤ (if PairProfile.Favoured a x y then |a| else 0) := by
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

private theorem favoured_nonneg
    (a : P.boundary → P.boundary → ℤ) (b : P.boundary → Bool) (v : P.boundary) :
    0 ≤ PairProfile.favouredWeight a b v :=
  Finset.sum_nonneg fun u _ => favoured_term_nonneg (a v u) (b v) (b u)

private theorem favoured_pos
    (a : P.boundary → P.boundary → ℤ) (b : P.boundary → Bool) (v u : P.boundary)
    (hfav : PairProfile.Favoured (a v u) (b v) (b u)) :
    0 < PairProfile.favouredWeight a b v := by
  classical
  have hpos : 0 < |a v u| := abs_pos.mpr
    (hfav.elim (fun h => ne_of_gt h.1) (fun h => ne_of_lt h.1))
  apply (Finset.sum_pos_iff_of_nonneg
    (fun w _ => favoured_term_nonneg (a v w) (b v) (b w))).mpr
  exact ⟨u, Finset.mem_univ u, by simpa only [if_pos hfav] using hpos⟩

theorem opponent_of_slack (M : Set V) (c : V → Bool)
    (hPM : (P.verts : Set V) ⊆ M) (hc : StrongMaximal G M c)
    (b : P.boundary → Bool) (hcb : P.Respects b c)
    (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (v : P.boundary)
    (hslack : PairProfile.weight a v < 2 * pieceDegree P.edges v.val) :
    ∃ w ∈ P.verts, G.Adj v.val w ∧ c w ≠ c v.val := by
  have hcert := P.opponent_certificate M c hPM hc b hcb K a hrep v
  apply P.exists_opponent_of_pos c v
  linarith [hcert.2, P.favoured_nonneg a b v]

theorem opponent_of_favoured (M : Set V) (c : V → Bool)
    (hPM : (P.verts : Set V) ⊆ M) (hc : StrongMaximal G M c)
    (b : P.boundary → Bool) (hcb : P.Respects b c)
    (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (v u : P.boundary)
    (hfav : PairProfile.Favoured (a v u) (b v) (b u)) :
    ∃ w ∈ P.verts, G.Adj v.val w ∧ c w ≠ c v.val := by
  have hcert := P.opponent_certificate M c hPM hc b hcb K a hrep v
  apply P.exists_opponent_of_pos c v
  linarith [hcert.1, hcert.2, P.favoured_pos a b v u hfav]

theorem exists_interaction_of_not_slack
    (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (v : P.boundary)
    (hn : ¬ PairProfile.weight a v < 2 * pieceDegree P.edges v.val) :
    ∃ u, v ≠ u ∧ a v u ≠ 0 := by
  classical
  by_contra hno
  have hz : ∀ u, a v u = 0 := by
    intro u
    by_cases hu : v = u
    · subst u
      exact hrep.2.1 v
    · exact Classical.byContradiction (fun hnu => hno ⟨u, hu, hnu⟩)
  have hw : PairProfile.weight a v = 0 := by simp [PairProfile.weight, hz]
  have hd := P.degree_pos v
  omega

theorem mem_boundary_of_adj {v w : V} (hv : v ∉ P.verts) (hw : w ∈ P.verts)
    (hvw : G.Adj v w) : v ∈ P.boundary := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(v, w), (P.edge_mem _).mpr ⟨hvw, Or.inr hw⟩, rfl⟩), hv⟩

end FinitePiece
end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyForcedWitness.lean. -/
/-!
# Forced opponents at boundary vertices of finite pieces

A boundary vertex `v` of a finite piece is *forced* by a boundary colouring `b`
when recolouring `v` does not raise the optimized score by the whole incidence
count of `v`. The profile Lipschitz bound makes this the exact criterion: `v`
is forced precisely when every maximizing interior colouring gives `v` an
opponent inside the piece. Only the direction used later is proved here.

Three consequences need no assumption on the size of the boundary and no pair
representation:

* a vertex that is not forced becomes forced after its own colour is reversed;
* that reversal keeps every other forced boundary vertex forced;
* for each colour of `v`, either some colouring of the other free boundary
  vertices forces `v`, or the opposite colour forces `v` under every colouring
  of them.

Pair representations are a sufficient condition: positive slack or one favoured
interaction forces the vertex.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy.FinitePiece

open scoped BigOperators

variable {V : Type u} {G : SimpleGraph V} (P : FinitePiece G)

/-- Recolouring the boundary vertex does not gain its entire incidence count. -/
def Forced (b : P.boundary → Bool) (v : P.boundary) : Prop :=
  P.profile (PairProfile.toggle b v) < P.profile b + pieceDegree P.edges v.val

/-- `x` lies on the boundary and is forced by the boundary colours of `c`. -/
def ForcedAt (c : V → Bool) (x : V) : Prop :=
  ∃ hx : x ∈ P.boundary, P.Forced (fun u => c u.val) ⟨x, hx⟩

/-- `x` is forced under every colouring that agrees with `q` on `T`. -/
def UniversalAt (T : Set V) (q : V → Bool) (x : V) : Prop :=
  ∀ c : V → Bool, Set.EqOn c q T → P.ForcedAt c x

/-- Being forced depends only on the colours of the boundary. -/
theorem forcedAt_congr (c c' : V → Bool) (h : Set.EqOn c c' (P.boundary : Set V)) (x : V)
    (hf : P.ForcedAt c x) : P.ForcedAt c' x := by
  obtain ⟨hx, hf⟩ := hf
  have heq : (fun u : P.boundary => c u.val) = fun u => c' u.val :=
    funext fun u => h u.property
  exact ⟨hx, heq ▸ hf⟩

theorem universalAt_mono {T T' : Set V} {q q' : V → Bool} (hT : T ⊆ T')
    (hq : Set.EqOn q' q T) (x : V) (h : P.UniversalAt T q x) : P.UniversalAt T' q' x :=
  fun c hc => h c fun _ hy => (hc (hT hy)).trans (hq hy)

/-- A forced boundary vertex has an opponent inside the piece in every colouring that
is strongly maximal on the piece. -/
theorem opponent_of_forcedAt (M : Set V) (c : V → Bool) (hPM : (P.verts : Set V) ⊆ M)
    (hc : StrongMaximal G M c) (x : V) (hf : P.ForcedAt c x) :
    ∃ w ∈ P.verts, G.Adj x w ∧ c w ≠ c x := by
  obtain ⟨hx, hf⟩ := hf
  have hresp : pieceDegree P.edges x + P.profile (fun u => c u.val) -
      P.profile (PairProfile.toggle (fun u => c u.val) ⟨x, hx⟩) ≤
        2 * pieceOpponents P.edges c x :=
    P.profile_response (fun u => c u.val) c (fun _ => rfl)
      (P.eq_profile_of_strongMaximal M c hPM hc (fun u => c u.val) (fun _ => rfl)) ⟨x, hx⟩
  have hf' : P.profile (PairProfile.toggle (fun u => c u.val) ⟨x, hx⟩) <
      P.profile (fun u => c u.val) + pieceDegree P.edges x := hf
  have hpos : 0 < pieceOpponents P.edges c x := by omega
  exact P.exists_opponent_of_pos c ⟨x, hx⟩ hpos

private theorem toggle_toggle (b : P.boundary → Bool) (v : P.boundary) :
    PairProfile.toggle (PairProfile.toggle b v) v = b := by
  classical
  funext u
  simp [PairProfile.toggle]

open Classical in
private theorem restrict_update (c : V → Bool) (x : V) (hx : x ∈ P.boundary) :
    (fun u : P.boundary => Function.update c x (!c x) u.val) =
      PairProfile.toggle (fun u : P.boundary => c u.val) ⟨x, hx⟩ := by
  funext u
  by_cases hu : u = ⟨x, hx⟩
  · subst hu
    simp [PairProfile.toggle]
  · have hval : u.val ≠ x := fun h => hu (Subtype.ext h)
    simp only [PairProfile.toggle, Function.update, dif_neg hval, dif_neg hu]

open Classical in
/-- A boundary vertex that is not forced becomes forced when its own colour is reversed. -/
theorem forcedAt_update_of_not (c : V → Bool) (x : V) (hx : x ∈ P.boundary)
    (h : ¬ P.ForcedAt c x) : P.ForcedAt (Function.update c x (!c x)) x := by
  refine ⟨hx, ?_⟩
  have hn : ¬ P.Forced (fun u => c u.val) ⟨x, hx⟩ := fun hf => h ⟨hx, hf⟩
  have hd := P.degree_pos ⟨x, hx⟩
  rw [P.restrict_update c x hx]
  unfold Forced at hn ⊢
  rw [P.toggle_toggle]
  omega

private theorem toggle_comm (b : P.boundary → Bool) (v u : P.boundary) (huv : u ≠ v) :
    PairProfile.toggle (PairProfile.toggle b v) u =
      PairProfile.toggle (PairProfile.toggle b u) v := by
  classical
  funext y
  by_cases hyu : y = u
  · subst hyu
    simp only [PairProfile.toggle, Function.update, dif_neg huv, dif_pos]
  · by_cases hyv : y = v
    · subst hyv
      simp only [PairProfile.toggle, Function.update, dif_neg hyu, dif_pos]
    · simp only [PairProfile.toggle, Function.update, dif_neg hyu, dif_neg hyv]

open Classical in
/-- Reversing the colour of a boundary vertex that is not forced keeps every other
forced boundary vertex forced. -/
theorem forcedAt_update_of_forcedAt (c : V → Bool) (x w : V) (hwx : w ≠ x)
    (hx : x ∈ P.boundary) (hnx : ¬ P.ForcedAt c x) (hw : P.ForcedAt c w) :
    P.ForcedAt (Function.update c x (!c x)) w := by
  obtain ⟨hwB, hwf⟩ := hw
  refine ⟨hwB, ?_⟩
  have hnf : ¬ P.Forced (fun u => c u.val) ⟨x, hx⟩ := fun h => hnx ⟨hx, h⟩
  have huv : (⟨w, hwB⟩ : P.boundary) ≠ ⟨x, hx⟩ := fun h => hwx (congrArg Subtype.val h)
  have hlip := P.profile_flip_bound
    (PairProfile.toggle (PairProfile.toggle (fun u => c u.val) ⟨w, hwB⟩) ⟨x, hx⟩) ⟨x, hx⟩
  rw [P.toggle_toggle] at hlip
  rw [P.restrict_update c x hx]
  unfold Forced at hwf hnf ⊢
  rw [P.toggle_comm _ ⟨x, hx⟩ ⟨w, hwB⟩ huv]
  omega

open Classical in
/-- **Servable or universal.** Fix the colours on `S` and the colour of the boundary
vertex `x ∉ S`. Either some colouring of the remaining vertices forces `x`, or the
opposite colour of `x` forces it under every colouring of the remaining vertices. -/
theorem servable_or_universal (S : Set V) (c : V → Bool) (x : V) (hxS : x ∉ S)
    (hx : x ∈ P.boundary) :
    (∃ c₁ : V → Bool, Set.EqOn c₁ c (S ∪ {x}) ∧ P.ForcedAt c₁ x) ∨
      P.UniversalAt (S ∪ {x}) (Function.update c x (!c x)) x := by
  by_cases h : ∃ c₁ : V → Bool, Set.EqOn c₁ c (S ∪ {x}) ∧ P.ForcedAt c₁ x
  · exact Or.inl h
  · refine Or.inr fun c₁ hc₁ => ?_
    have hc₁x : c₁ x = !c x := (hc₁ (Or.inr rfl)).trans (Function.update_self ..)
    have hc₀ : Set.EqOn (Function.update c₁ x (!c₁ x)) c (S ∪ {x}) := by
      intro y hy
      rcases hy with hyS | hyx
      · have hne : y ≠ x := fun e => hxS (e ▸ hyS)
        exact (Function.update_of_ne hne _ _).trans
          ((hc₁ (Or.inl hyS)).trans (Function.update_of_ne hne _ _))
      · have hyx' : y = x := hyx
        rw [hyx', Function.update_self, hc₁x, Bool.not_not]
    have hflip := P.forcedAt_update_of_not _ x hx (fun hf => h ⟨_, hc₀, hf⟩)
    have hback : Function.update (Function.update c₁ x (!c₁ x)) x
        (!Function.update c₁ x (!c₁ x) x) = c₁ := by
      funext y
      by_cases hy : y = x
      · rw [hy]
        simp
      · simp [Function.update_of_ne hy]
    rw [hback] at hflip
    exact hflip

open Classical in
private theorem favouredWeight_nonneg (a : P.boundary → P.boundary → ℤ)
    (b : P.boundary → Bool) (v : P.boundary) : 0 ≤ PairProfile.favouredWeight a b v := by
  unfold PairProfile.favouredWeight
  refine Finset.sum_nonneg fun u _ => ?_
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

open Classical in
private theorem favouredWeight_pos (a : P.boundary → P.boundary → ℤ)
    (b : P.boundary → Bool) (v u : P.boundary)
    (hfav : PairProfile.Favoured (a v u) (b v) (b u)) :
    0 < PairProfile.favouredWeight a b v := by
  have hpos : 0 < |a v u| := abs_pos.mpr
    (hfav.elim (fun h => ne_of_gt h.1) (fun h => ne_of_lt h.1))
  have hnon : ∀ w ∈ (Finset.univ : Finset P.boundary), 0 ≤
      (if PairProfile.Favoured (a v w) (b v) (b w) then |a v w| else 0) := by
    intro w _
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  unfold PairProfile.favouredWeight
  apply (Finset.sum_pos_iff_of_nonneg hnon).mpr
  exact ⟨u, Finset.mem_univ u, by simpa only [if_pos hfav] using hpos⟩

private theorem forced_of_certificate (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (b : P.boundary → Bool) (v : P.boundary)
    (h : 0 < 2 * pieceDegree P.edges v.val - PairProfile.weight a v +
      2 * PairProfile.favouredWeight a b v) : P.Forced b v := by
  have hflip := P.profile_flip_bound (PairProfile.toggle b v) v
  rw [P.toggle_toggle] at hflip
  have hcert : PairProfile.weight a v ≤ 2 * pieceDegree P.edges v.val ∧
      2 * pieceDegree P.edges v.val - PairProfile.weight a v +
        2 * PairProfile.favouredWeight a b v ≤
          4 * (pieceDegree P.edges v.val + P.profile b -
            P.profile (PairProfile.toggle b v)) :=
    PairProfile.universal_opponent_certificate P.profile K a hrep
      (fun v => pieceDegree P.edges v.val) P.profile_flip_bound b v
      (pieceDegree P.edges v.val + P.profile b - P.profile (PairProfile.toggle b v))
      (by omega)
  unfold Forced
  omega

/-- Positive slack in a pair representation forces the vertex under every boundary
colouring. -/
theorem forced_of_slack (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (b : P.boundary → Bool) (v : P.boundary)
    (hslack : PairProfile.weight a v < 2 * pieceDegree P.edges v.val) : P.Forced b v :=
  P.forced_of_certificate K a hrep b v (by linarith [P.favouredWeight_nonneg a b v])

/-- One favoured interaction of a pair representation forces the vertex, whatever the
other boundary colours are. -/
theorem forced_of_favoured (K : ℤ) (a : P.boundary → P.boundary → ℤ)
    (hrep : PairProfile.Represents P.profile K a) (b : P.boundary → Bool)
    (v u : P.boundary) (hfav : PairProfile.Favoured (a v u) (b v) (b u)) :
    P.Forced b v := by
  have hw : PairProfile.weight a v ≤ 2 * pieceDegree P.edges v.val :=
    PairProfile.weight_budget P.profile K a hrep (fun v => pieceDegree P.edges v.val)
      P.profile_flip_bound v
  exact P.forced_of_certificate K a hrep b v
    (by linarith [P.favouredWeight_pos a b v u hfav])

end TenChallenges.Continuation.Energy.FinitePiece

/- Inlined from Continuation/UnfriendlyFreshSelection.lean. -/
/-!
# Fresh selection of permanent witnesses

A countable set of vertices is coloured in finitely many commitments per stage.
Each stage serves one vertex with a witness whose finite support is committed
at once, so the witness is permanent. A vertex is served again for every finite
set of forbidden keys, which makes its witness set infinite.

The service hypothesis is the only place where a combinatorial structure enters.
No limit of recolourings is taken: committed colours never change.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.FreshSelection

variable {V : Type u} {Λ : Type v}

/-- Colours prescribed on `S` extend so that every vertex of `J` has infinitely
many witnesses, provided that each vertex of `J` can always be served: for every
finite set `D` of committed vertices, every finite set `F` of forbidden keys and
every current colouring, some witness with key outside `F` holds after changing
colours only outside `D ∪ S`. -/
theorem exists_fresh_selection [Countable V] (S J : Set V) (q : V → Bool)
    (key : Λ → V) (supp : Λ → V → Finset V)
    (Wit : Λ → V → (V → Bool) → Prop)
    (hlocal : ∀ (j : Λ) (v : V) (c c' : V → Bool),
      Set.EqOn c c' (supp j v) → Wit j v c → Wit j v c')
    (hserve : ∀ v ∈ J, ∀ (D F : Finset V) (c : V → Bool),
      ∃ (j : Λ) (c' : V → Bool), key j ∉ F ∧ Set.EqOn c' q S ∧
        Set.EqOn c' c (↑D \ S) ∧ Wit j v c') :
    ∃ c : V → Bool, Set.EqOn c q S ∧ ∀ v ∈ J, {j | Wit j v c}.Infinite := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · exact ⟨q, fun _ _ => rfl, fun v hv => hv.elim⟩
  · haveI : Nonempty J := hJ.to_subtype
    -- Schedule every vertex of `J` together with every finite forbidden key set.
    obtain ⟨e, he⟩ := exists_surjective_nat (J × Finset V)
    choose pick col hkey hS hD hW using fun v : J => hserve v.val v.property
    let s : ℕ → Finset V × (V → Bool) :=
      Nat.rec (∅, q) (fun n st =>
        (st.1 ∪ supp (pick (e n).1 st.1 (e n).2 st.2) (e n).1.val,
          col (e n).1 st.1 (e n).2 st.2))
    have hDstep : ∀ n, (s n).1 ⊆ (s (n + 1)).1 := fun n => Finset.subset_union_left
    have hDmono : Monotone (fun n => (s n).1) := monotone_nat_of_le_succ hDstep
    have hSall : ∀ n, Set.EqOn (s n).2 q S := by
      intro n
      cases n with
      | zero => exact fun _ _ => rfl
      | succ n => exact hS (e n).1 (s n).1 (e n).2 (s n).2
    -- Committed colours outside `S` never change.
    have hcolstep : ∀ n y, y ∈ (s n).1 → y ∉ S → (s (n + 1)).2 y = (s n).2 y :=
      fun n y hy hyS => hD (e n).1 (s n).1 (e n).2 (s n).2 ⟨hy, hyS⟩
    have hcoh : ∀ {m n : ℕ}, m ≤ n → ∀ y ∈ (s m).1, (s n).2 y = (s m).2 y := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => exact fun _ _ => rfl
      | succ k hmk ih =>
        intro y hy
        by_cases hyS : y ∈ S
        · exact (hSall (k + 1) hyS).trans (hSall m hyS).symm
        · exact (hcolstep k y (hDmono hmk hy) hyS).trans (ih y hy)
    let c : V → Bool := fun y =>
      if h : ∃ n, y ∈ (s n).1 then (s (Classical.choose h)).2 y else q y
    have hc : ∀ n, ∀ y ∈ (s n).1, c y = (s n).2 y := by
      intro n y hy
      have h : ∃ n, y ∈ (s n).1 := ⟨n, hy⟩
      have hval : c y = (s (Classical.choose h)).2 y := dif_pos h
      rw [hval]
      exact (hcoh (Nat.le_max_right n (Classical.choose h)) y
        (Classical.choose_spec h)).symm.trans
          (hcoh (Nat.le_max_left n (Classical.choose h)) y hy)
    have hcS : Set.EqOn c q S := by
      intro y hy
      by_cases h : ∃ n, y ∈ (s n).1
      · exact (dif_pos h).trans (hSall _ hy)
      · exact dif_neg h
    -- The witness chosen at a stage survives, since its support was committed.
    have hrequest : ∀ n, ∃ j, key j ∉ (e n).2 ∧ Wit j (e n).1.val c := fun n =>
      ⟨pick (e n).1 (s n).1 (e n).2 (s n).2, hkey (e n).1 (s n).1 (e n).2 (s n).2,
        hlocal _ _ (s (n + 1)).2 c
          (fun y hy => (hc (n + 1) y (Finset.mem_union_right _ hy)).symm)
          (hW (e n).1 (s n).1 (e n).2 (s n).2)⟩
    refine ⟨c, hcS, fun v hv hfin => ?_⟩
    obtain ⟨n, hn⟩ := he (⟨v, hv⟩, (hfin.image key).toFinset)
    obtain ⟨j, hjF, hjW⟩ := hrequest n
    rw [hn] at hjF hjW
    exact hjF ((hfin.image key).mem_toFinset.mpr ⟨j, hjW, rfl⟩)

end TenChallenges.Continuation.FreshSelection

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

/- Inlined from Continuation/UnfriendlyRobustSteps.lean. -/
/-!
# Further extension steps for robust colourings of infinite-degree vertices

A maximal robust frozen colouring (see `UnfriendlyRecurrentBlocks`) cannot be extended by
any of three steps: a recurrent block, a vertex with infinitely many frozen neighbours, or
a set of vertices each having infinitely many neighbours inside the set. A finite set of
remaining infinite-degree vertices is then absorbed by finite repairs, which keep the
colouring strongly maximal and therefore keep every robust witness.

This is a special case of the countable unfriendly partition problem. It does not prove
the unrestricted conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.Energy

variable {V : Type u}

open Classical in
/-- Recurrent blocks are monotone in the frozen set: enlarging it only removes vertices
from the block. -/
theorem RecurrentBlock.relativize (G : SimpleGraph V) (S₀ S : Set V) (hS : S₀ ⊆ S)
    (B : Finset V) (h : RecurrentBlock G S₀ B) :
    RecurrentBlock G S (B.filter (· ∉ S)) := by
  obtain ⟨C, hdisj, hfin, hbdry, htouch⟩ := h
  refine ⟨C, hdisj, hfin, ?_, fun i u hu => htouch i u (Finset.mem_filter.mp hu).1⟩
  intro i x hx y hxy
  rcases hbdry i x hx y hxy with hC | hB | hE
  · exact Or.inl hC
  · by_cases hyS : y ∈ S
    · exact Or.inr (Or.inr hyS)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hB, hyS⟩))
  · exact Or.inr (Or.inr (hS hE))

/-- A vertex with infinitely many frozen neighbours can be frozen with the colour opposite
to infinitely many of them. -/
theorem Robust.extend_frozen_neighbors (G : SimpleGraph V) (M S : Set V) (q : V → Bool)
    (hq : Robust G M S q) (v : V) (hvS : v ∉ S)
    (hinf : (G.neighborSet v ∩ S).Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M (S ∪ {v}) q' := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Bool, {w | G.Adj v w ∧ w ∈ S ∧ q w = b}.Infinite := by
    by_contra hno
    have hf : ∀ b : Bool, {w | G.Adj v w ∧ w ∈ S ∧ q w = b}.Finite := fun b =>
      Set.not_infinite.mp fun hi => hno ⟨b, hi⟩
    refine hinf (((hf true).union (hf false)).subset fun w hw => ?_)
    cases hqw : q w
    · exact Or.inr ⟨hw.1, hw.2, hqw⟩
    · exact Or.inl ⟨hw.1, hw.2, hqw⟩
  have hq'S : Set.EqOn (Function.update q v (!b)) q S := fun y hy =>
    Function.update_of_ne (show y ≠ v from fun h => hvS (h ▸ hy)) _ _
  refine ⟨Function.update q v (!b), hq'S, ?_⟩
  intro c hc hcq u hu
  have hcS : Set.EqOn c q S := fun y hy => (hcq (Or.inl hy)).trans (hq'S hy)
  rcases hu with huS | huv
  · exact hq c hc hcS u huS
  · obtain rfl : u = v := huv
    have hcu : c u = !b := (hcq (Or.inr rfl)).trans (Function.update_self ..)
    refine hb.mono fun w hw => ⟨hw.1, ?_⟩
    rw [hcS hw.2.1, hw.2.2, hcu]
    cases b <;> simp

private theorem induce_neighbors_infinite (G : SimpleGraph V) (R : Set V)
    (hR : ∀ v ∈ R, (G.neighborSet v ∩ R).Infinite) :
    ∀ x : R, ((G.induce R).neighborSet x).Infinite := by
  intro x
  apply Set.Infinite.of_image (Subtype.val : R → V)
  simpa [SimpleGraph.neighborSet_induce, Set.image_preimage_eq_inter_range] using
    hR x.val x.property

private theorem exists_boolean_unfriendly_of_infinite_degrees [Countable V]
    (G : SimpleGraph V) (hG : ∀ x, (G.neighborSet x).Infinite) :
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

/-- A set of unfrozen vertices, each with infinitely many neighbours inside the set, can be
frozen all at once: the induced graph has infinite minimum degree. -/
theorem Robust.extend_core [Countable V] (G : SimpleGraph V) (M S : Set V) (q : V → Bool)
    (hq : Robust G M S q) (J : Set V) (hJS : ∀ v ∈ J, v ∉ S)
    (hJ : ∀ v ∈ J, (G.neighborSet v ∩ J).Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M (S ∪ J) q' := by
  classical
  obtain ⟨cJ, hcJ⟩ := exists_boolean_unfriendly_of_infinite_degrees (G.induce J)
    (induce_neighbors_infinite G J hJ)
  let q' : V → Bool := fun w => if hw : w ∈ J then cJ ⟨w, hw⟩ else q w
  have hq'S : Set.EqOn q' q S := fun y hy => dif_neg (fun hyJ => hJS y hyJ hy)
  refine ⟨q', hq'S, ?_⟩
  intro c hc hcq v hv
  rcases hv with hvS | hvJ
  · exact hq c hc (fun y hy => (hcq (Or.inl hy)).trans (hq'S hy)) v hvS
  · have hcJ' : ∀ x : J, c x.val = cJ x := fun x =>
      (hcq (Or.inr x.property)).trans (dif_pos x.property)
    have hi := infinite_opposite_of_unfriendly (G.induce J) cJ ⟨v, hvJ⟩
      (induce_neighbors_infinite G J hJ ⟨v, hvJ⟩) (hcJ ⟨v, hvJ⟩)
    refine (hi.image (fun _ _ _ _ h => Subtype.ext h)).mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hy.1, fun heq => hy.2 ((hcJ' y).symm.trans (heq.trans (hcJ' ⟨v, hvJ⟩)))⟩

/-- Finitely many infinite-degree vertices outside `A` and outside a fixed set `D` can
acquire infinite opposite neighbourhoods, keeping strong maximality on `A` and all colours
on `D`. -/
theorem finite_hub_stage_fixing [Countable V] (G : SimpleGraph V)
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

/-- A robust frozen colouring of all but finitely many infinite-degree vertices yields an
unfriendly partition: the finite remainder is repaired without leaving the strongly
maximal colourings that agree with the frozen colours. -/
theorem exists_unfriendly_of_robust_cofinite [Countable V] (G : SimpleGraph V)
    (S : Set V) (q : V → Bool)
    (hS : S ⊆ {v | (G.neighborSet v).Infinite})
    (hq : Robust G {v | (G.neighborSet v).Infinite}ᶜ S q)
    (hfin : ({v | (G.neighborSet v).Infinite} \ S).Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  classical
  obtain ⟨c0, hc0q, hc0⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
    {v | (G.neighborSet v).Infinite} q
  obtain ⟨c, hcS, hc, hgood⟩ := finite_hub_stage_fixing G
    {v | (G.neighborSet v).Infinite}ᶜ S (fun v hv hvc => hvc (hS hv)) c0 hc0 hfin.toFinset
    (fun v hv => ⟨(hfin.mem_toFinset.mp hv).1, fun hvc => hvc (hfin.mem_toFinset.mp hv).1,
      (hfin.mem_toFinset.mp hv).2⟩)
  refine ⟨fun v => some (c v), fun v => ?_⟩
  by_cases hN : (G.neighborSet v).Finite
  · exact unfriendlyAt_of_strongMaximal G _ c hc v (fun hInf => hInf hN) hN
  · apply unfriendly_of_infinite_opposite G c v
    by_cases hvS : v ∈ S
    · exact hq c hc (fun y hy => (hcS hy).trans (hc0q (hS hy))) v hvS
    · exact hgood v (hfin.mem_toFinset.mpr ⟨hN, hvS⟩)

/-- **Robust exhaustion.** Suppose that whenever a set `S` of infinite-degree vertices
leaves infinitely many of them outside, one of three steps is available: a nonempty
recurrent block over `S`, a further vertex with infinitely many neighbours in `S`, or a
nonempty set of further vertices each having infinitely many neighbours in that set.
Then the countable graph has an unfriendly partition. -/
theorem exists_unfriendly_of_robust_steps [Countable V] (G : SimpleGraph V)
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      ({v | (G.neighborSet v).Infinite} \ S).Infinite →
      (∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) ∨
      (∃ v, (G.neighborSet v).Infinite ∧ v ∉ S ∧ (G.neighborSet v ∩ S).Infinite) ∨
      (∃ J : Set V, J.Nonempty ∧ (∀ v ∈ J, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        ∀ v ∈ J, (G.neighborSet v ∩ J).Infinite)) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  obtain ⟨S, q, hSH, hrob, hmax⟩ := exists_maximal_robust G
    {v | (G.neighborSet v).Infinite}ᶜ {v | (G.neighborSet v).Infinite}
  by_cases hfin : ({v | (G.neighborSet v).Infinite} \ S).Finite
  · exact exists_unfriendly_of_robust_cofinite G S q hSH hrob hfin
  · exfalso
    rcases h S hSH hfin with ⟨A, ⟨a, ha⟩, hA, hblock⟩ | ⟨v, hvI, hvS, hinf⟩ |
      ⟨J, ⟨j, hj⟩, hJ, hJinf⟩
    · obtain ⟨q', hq'q, hq'⟩ := Robust.extend_block G _ S q hrob A (fun v hv => (hA v hv).2)
        (fun v hv => (hA v hv).1) (fun x hx hinf => hinf hx) hblock
      exact (hA a ha).2 (hmax (S ∪ (A : Set V)) q'
        (Set.union_subset hSH (fun v hv => (hA v hv).1)) hq' Set.subset_union_left hq'q
        (Or.inr ha))
    · obtain ⟨q', hq'q, hq'⟩ := Robust.extend_frozen_neighbors G _ S q hrob v hvS hinf
      exact hvS (hmax (S ∪ {v}) q'
        (Set.union_subset hSH (Set.singleton_subset_iff.mpr hvI)) hq' Set.subset_union_left
        hq'q (Or.inr rfl))
    · obtain ⟨q', hq'q, hq'⟩ := Robust.extend_core G _ S q hrob J (fun v hv => (hJ v hv).2)
        hJinf
      exact (hJ j hj).2 (hmax (S ∪ J) q'
        (Set.union_subset hSH (fun v hv => (hJ v hv).1)) hq' Set.subset_union_left hq'q
        (Or.inr hj))

/-- **Recurrent or hub-rich.** A countable graph has an unfriendly partition if all but
finitely many of its infinite-degree vertices either lie in a recurrent finite boundary of
infinite-degree vertices or have infinitely many infinite-degree neighbours. -/
theorem exists_unfriendly_of_recurrent_or_hub_rich [Countable V] (G : SimpleGraph V)
    (h : {v | (G.neighborSet v).Infinite ∧
        (¬ ∃ B : Finset V, v ∈ B ∧ (∀ u ∈ B, (G.neighborSet u).Infinite) ∧
          RecurrentBlock G ∅ B) ∧
        (G.neighborSet v ∩ {w | (G.neighborSet w).Infinite}).Finite}.Finite) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  classical
  refine exists_unfriendly_of_robust_steps G fun S hSH hinfS => ?_
  by_cases hrec : ∃ v, (G.neighborSet v).Infinite ∧ v ∉ S ∧
      ∃ B : Finset V, v ∈ B ∧ (∀ u ∈ B, (G.neighborSet u).Infinite) ∧ RecurrentBlock G ∅ B
  · obtain ⟨v, _, hvS, B, hvB, hBI, hB⟩ := hrec
    exact Or.inl ⟨B.filter (· ∉ S), ⟨v, Finset.mem_filter.mpr ⟨hvB, hvS⟩⟩,
      fun u hu => ⟨hBI u (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩,
      RecurrentBlock.relativize G ∅ S (Set.empty_subset S) B hB⟩
  · by_cases hfro : ∃ v, (G.neighborSet v).Infinite ∧ v ∉ S ∧ (G.neighborSet v ∩ S).Infinite
    · exact Or.inr (Or.inl hfro)
    · refine Or.inr (Or.inr ⟨_, (hinfS.sdiff h).nonempty,
        fun v hv => ⟨hv.1.1, hv.1.2⟩, fun v hv => ?_⟩)
      have hhub : (G.neighborSet v ∩ {w | (G.neighborSet w).Infinite}).Infinite := fun hf =>
        hv.2 ⟨hv.1.1, fun hB => hrec ⟨v, hv.1.1, hv.1.2, hB⟩, hf⟩
      have hSfin : (G.neighborSet v ∩ S).Finite :=
        Set.not_infinite.mp fun hi => hfro ⟨v, hv.1.1, hv.1.2, hi⟩
      refine (hhub.sdiff (hSfin.union h)).mono fun w hw => ?_
      exact ⟨hw.1.1, ⟨hw.1.2, fun hwS => hw.2 (Or.inl ⟨hw.1.1, hwS⟩)⟩,
        fun hwX => hw.2 (Or.inr hwX)⟩

end TenChallenges.Continuation.Energy

/- Inlined from Continuation/UnfriendlyFreshWitness.lean. -/
/-!
# Fresh finite pieces as permanent witnesses

A robust frozen colouring is first enlarged to a maximal one. Maximality rules out
three kinds of further robust steps, and what remains can be served greedily:

* a vertex with infinitely many frozen neighbours;
* a vertex that infinitely many pieces force with one colour, whatever the other
  free boundary colours are;
* a finite set that is the exact free boundary of infinitely many pieces;
* two vertices joined by nonzero pair interactions in infinitely many pieces.

After these exclusions every remaining vertex can be given a new permanent witness
at each finite stage, using a neighbour or a piece whose other free boundary
vertices have not been coloured yet. No bound on the boundary size of a piece and
no pair representation is needed for that last step.

This is a special case of the countable unfriendly partition problem. It does not
prove the unrestricted conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

namespace Energy

variable {V : Type u}

/-- No robust frozen colouring inside `H` properly extends `(S, q)`. -/
def MaximalRobust (G : SimpleGraph V) (M S H : Set V) (q : V → Bool) : Prop :=
  ∀ (S' : Set V) (q' : V → Bool), S' ⊆ H → Robust G M S' q' → S ⊆ S' →
    Set.EqOn q' q S → S' ⊆ S

/-- Maximal robust frozen colourings exist above any robust frozen colouring. -/
theorem exists_maximal_robust_extending (G : SimpleGraph V) (M H S₀ : Set V)
    (q₀ : V → Bool) (hS₀ : S₀ ⊆ H) (hq₀ : Robust G M S₀ q₀) :
    ∃ (S : Set V) (q : V → Bool), S₀ ⊆ S ∧ S ⊆ H ∧ Set.EqOn q q₀ S₀ ∧
      Robust G M S q ∧ MaximalRobust G M S H q := by
  classical
  let T : Type u := {P : Set V × (V → Bool) //
    S₀ ⊆ P.1 ∧ P.1 ⊆ H ∧ Set.EqOn P.2 q₀ S₀ ∧ Robust G M P.1 P.2}
  let r : T → T → Prop := fun P Q => P.1.1 ⊆ Q.1.1 ∧ Set.EqOn Q.1.2 P.1.2 P.1.1
  have htrans : ∀ {a b c : T}, r a b → r b c → r a c := fun {a b c} hab hbc =>
    ⟨hab.1.trans hbc.1, fun y hy => (hbc.2 (hab.1 hy)).trans (hab.2 hy)⟩
  have hchain : ∀ c : Set T, IsChain r c → ∃ ub, ∀ a ∈ c, r a ub := by
    intro c hc
    let dom : Set V := S₀ ∪ ⋃ P ∈ c, P.1.1
    let col : V → Bool := fun y =>
      if h : ∃ P ∈ c, y ∈ P.1.1 then (Classical.choose h).1.2 y else q₀ y
    have hcol : ∀ P ∈ c, Set.EqOn col P.1.2 P.1.1 := by
      intro P hP y hy
      have h : ∃ P ∈ c, y ∈ P.1.1 := ⟨P, hP, hy⟩
      have hspec := Classical.choose_spec h
      have hval : col y = (Classical.choose h).1.2 y := dif_pos h
      rw [hval]
      by_cases hPQ : Classical.choose h = P
      · rw [hPQ]
      · rcases hc hspec.1 hP hPQ with hle | hle
        · exact (hle.2 hspec.2).symm
        · exact hle.2 hy
    have hcol₀ : Set.EqOn col q₀ S₀ := by
      intro y hy
      by_cases h : ∃ P ∈ c, y ∈ P.1.1
      · exact (dif_pos h).trans ((Classical.choose h).2.2.2.1 hy)
      · exact dif_neg h
    have hdomH : dom ⊆ H :=
      Set.union_subset hS₀ (Set.iUnion₂_subset fun P _ => P.2.2.1)
    have hrob : Robust G M dom col := by
      intro cc hcc heq v hv
      rcases hv with hv₀ | hv
      · exact hq₀ cc hcc (fun y hy => (heq (Or.inl hy)).trans (hcol₀ hy)) v hv₀
      · obtain ⟨P, hP, hvP⟩ := Set.mem_iUnion₂.mp hv
        exact P.2.2.2.2 cc hcc
          (fun y hy => (heq (Or.inr (Set.mem_iUnion₂.mpr ⟨P, hP, hy⟩))).trans
            (hcol P hP hy)) v hvP
    exact ⟨⟨(dom, col), Set.subset_union_left, hdomH, hcol₀, hrob⟩, fun P hP =>
      ⟨fun y hy => Or.inr (Set.mem_iUnion₂.mpr ⟨P, hP, hy⟩), hcol P hP⟩⟩
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hchain htrans
  refine ⟨m.1.1, m.1.2, m.2.1, m.2.2.1, m.2.2.2.1, m.2.2.2.2,
    fun S' q' hS'H hrob hSS' heq => ?_⟩
  exact (hm ⟨(S', q'), m.2.1.trans hSS', hS'H,
    fun y hy => (heq (m.2.1 hy)).trans (m.2.2.2.1 hy), hrob⟩ ⟨hSS', heq⟩).1

end Energy

open Energy

variable {V : Type u} {ι : Type v}

/-- Pairwise disjoint finite pieces of finite-degree vertices. -/
structure PieceFamily (G : SimpleGraph V) (ι : Type v) where
  piece : ι → Energy.FinitePiece G
  disjoint : Pairwise (Function.onFun Disjoint (fun i => (piece i).verts))

namespace PieceFamily

variable {G : SimpleGraph V} (D : PieceFamily G ι)

theorem finite_pieces_meeting {O : Set V} (hO : O.Finite) :
    {i | ∃ w ∈ O, w ∈ (D.piece i).verts}.Finite := by
  have hf : ∀ w : V, {i | w ∈ (D.piece i).verts}.Subsingleton := by
    intro w i hi j hj
    by_contra hij
    exact Finset.disjoint_left.mp (D.disjoint hij) hi hj
  exact (hO.biUnion (fun w _ => (hf w).finite)).subset
    (fun i ⟨w, hw, hwi⟩ => Set.mem_iUnion₂.mpr ⟨w, hw, hwi⟩)

theorem piece_subset (M : Set V) (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (i : ι) :
    ((D.piece i).verts : Set V) ⊆ M :=
  fun x hx => hM x ((D.piece i).finite_degree x hx)

/-- Opponents inside infinitely many pieces are infinitely many opponents. -/
theorem infinite_opposite_of_pieces (c : V → Bool) (x : V)
    (h : {i | ∃ w ∈ (D.piece i).verts, G.Adj x w ∧ c w ≠ c x}.Infinite) :
    (oppositeSet G c x).Infinite := fun hO =>
  h ((D.finite_pieces_meeting hO).subset
    fun _ ⟨w, hw, hadj, hne⟩ => ⟨w, ⟨hadj, hne⟩, hw⟩)

open Classical in
/-- **Universal step.** A vertex that infinitely many pieces force with the colour `β`,
under every colouring of the vertices outside `S ∪ {x}`, can be frozen with `β`. -/
theorem robust_update_of_universal (M S : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hq : Robust G M S q)
    (x : V) (hx : x ∉ S) (β : Bool)
    (hinf : {i | (D.piece i).UniversalAt (S ∪ {x}) (Function.update q x β) x}.Infinite) :
    Robust G M (S ∪ {x}) (Function.update q x β) := by
  intro c hc hcq v hv
  rcases hv with hvS | hvx
  · exact hq c hc (fun y hy => (hcq (Or.inl hy)).trans
      (Function.update_of_ne (fun h : y = x => hx (h ▸ hy)) _ _)) v hvS
  · have hvx' : v = x := hvx
    rw [hvx']
    apply D.infinite_opposite_of_pieces c x
    exact hinf.mono fun i
        (hi : (D.piece i).UniversalAt (S ∪ {x}) (Function.update q x β) x) =>
      (D.piece i).opponent_of_forcedAt M c (D.piece_subset M hM i) hc x (hi c hcq)

open Classical in
private theorem robust_update_of_favoured_pair (M S : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hq : Robust G M S q)
    (x p : V) (hx : x ∉ S) (hp : p ∉ S) (hxp : x ≠ p) (γ : Bool)
    (hinf : {i | ∃ (K : ℤ) (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
        (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
        PairProfile.Represents (D.piece i).profile K a ∧
          PairProfile.Favoured (a ⟨x, hx⟩ ⟨p, hp⟩) false γ}.Infinite) :
    Robust G M (S ∪ {x, p}) (Function.update (Function.update q x false) p γ) := by
  intro c hc hcq v hv
  have hcx : c x = false := (hcq (Or.inr (Or.inl rfl))).trans
    ((Function.update_of_ne hxp _ _).trans (Function.update_self ..))
  have hcp : c p = γ := (hcq (Or.inr (Or.inr rfl))).trans (Function.update_self ..)
  rcases hv with hvS | hvx | hvp
  · refine hq c hc (fun y hy => (hcq (Or.inl hy)).trans ?_) v hvS
    exact (Function.update_of_ne (fun h : y = p => hp (h ▸ hy)) _ _).trans
      (Function.update_of_ne (fun h : y = x => hx (h ▸ hy)) _ _)
  · have hvx' : v = x := hvx
    rw [hvx']
    apply D.infinite_opposite_of_pieces c x
    refine hinf.mono fun i hi => ?_
    obtain ⟨K, a, hxB, hpB, hrep, hfav⟩ := hi
    refine (D.piece i).opponent_of_forcedAt M c (D.piece_subset M hM i) hc x ⟨hxB, ?_⟩
    apply (D.piece i).forced_of_favoured K a hrep (fun u => c u.val) ⟨x, hxB⟩ ⟨p, hpB⟩
    show PairProfile.Favoured (a ⟨x, hxB⟩ ⟨p, hpB⟩) (c x) (c p)
    rw [hcx, hcp]
    exact hfav
  · have hvp' : v = p := hvp
    rw [hvp']
    apply D.infinite_opposite_of_pieces c p
    refine hinf.mono fun i hi => ?_
    obtain ⟨K, a, hxB, hpB, hrep, hfav⟩ := hi
    refine (D.piece i).opponent_of_forcedAt M c (D.piece_subset M hM i) hc p ⟨hpB, ?_⟩
    apply (D.piece i).forced_of_favoured K a hrep (fun u => c u.val) ⟨p, hpB⟩ ⟨x, hxB⟩
    show PairProfile.Favoured (a ⟨p, hpB⟩ ⟨x, hxB⟩) (c p) (c x)
    rw [hrep.1 ⟨p, hpB⟩ ⟨x, hxB⟩, hcx, hcp]
    exact hfav.elim (fun h => Or.inl ⟨h.1, h.2.symm⟩) (fun h => Or.inr ⟨h.1, h.2.symm⟩)

/-- **Pair step.** Two unfrozen vertices joined by a nonzero pair interaction in
infinitely many pieces can be frozen together. -/
theorem exists_robust_of_pair (M S : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hq : Robust G M S q)
    (x p : V) (hx : x ∉ S) (hp : p ∉ S) (hxp : x ≠ p)
    (hinf : {i | ∃ (K : ℤ) (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
        (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
        PairProfile.Represents (D.piece i).profile K a ∧ a ⟨x, hx⟩ ⟨p, hp⟩ ≠ 0}.Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M (S ∪ {x, p}) q' := by
  classical
  have hsplit : ∃ γ : Bool, {i | ∃ (K : ℤ)
      (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
      (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
      PairProfile.Represents (D.piece i).profile K a ∧
        PairProfile.Favoured (a ⟨x, hx⟩ ⟨p, hp⟩) false γ}.Infinite := by
    by_contra hno
    have hf : ∀ γ : Bool, {i | ∃ (K : ℤ)
        (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
        (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
        PairProfile.Represents (D.piece i).profile K a ∧
          PairProfile.Favoured (a ⟨x, hx⟩ ⟨p, hp⟩) false γ}.Finite :=
      fun γ => Set.not_infinite.mp fun hi => hno ⟨γ, hi⟩
    refine hinf (((hf true).union (hf false)).subset ?_)
    rintro i ⟨K, a, hxB, hpB, hrep, hne⟩
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact Or.inr ⟨K, a, hxB, hpB, hrep, Or.inr ⟨hneg, rfl⟩⟩
    · exact Or.inl ⟨K, a, hxB, hpB, hrep, Or.inl ⟨hpos, by decide⟩⟩
  obtain ⟨γ, hγ⟩ := hsplit
  refine ⟨Function.update (Function.update q x false) p γ, fun y hy => ?_,
    D.robust_update_of_favoured_pair M S q hM hq x p hx hp hxp γ hγ⟩
  exact (Function.update_of_ne (fun h : y = p => hp (h ▸ hy)) _ _).trans
    (Function.update_of_ne (fun h : y = x => hx (h ▸ hy)) _ _)

open Classical in
/-- Infinitely many pieces with the same free boundary form a recurrent block. -/
theorem recurrentBlock_of_infinite (S : Set V) (A : Finset V)
    (hinf : {i | (D.piece i).boundary.filter (· ∉ S) = A}.Infinite) :
    RecurrentBlock G S A := by
  let f := hinf.natEmbedding
  have hf : ∀ n, (D.piece (f n).val).boundary.filter (· ∉ S) = A := fun n => (f n).property
  refine ⟨fun n => (D.piece (f n).val).verts, ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    exact D.disjoint fun h => hmn (f.injective (Subtype.ext h))
  · intro n x hx
    exact (D.piece (f n).val).finite_degree x hx
  · intro n x hx y hxy
    by_cases hy : y ∈ (D.piece (f n).val).verts
    · exact Or.inl hy
    · have hyB := (D.piece (f n).val).mem_boundary_of_adj hy hx hxy.symm
      by_cases hyS : y ∈ S
      · exact Or.inr (Or.inr hyS)
      · refine Or.inr (Or.inl ?_)
        rw [← hf n]
        exact Finset.mem_filter.mpr ⟨hyB, hyS⟩
  · intro n v hv
    rw [← hf n] at hv
    obtain ⟨w, hw, hadj⟩ :=
      (D.piece (f n).val).boundary_touch ⟨v, (Finset.mem_filter.mp hv).1⟩
    exact ⟨w, hw, hadj⟩

/-- Witness identities: a neighbour, or a piece together with one of its vertices and the
set of boundary vertices whose colours certify the witness. -/
abbrev WitnessIndex (D : PieceFamily G ι) :=
  V ⊕ (Σ i : ι, {w : V // w ∈ (D.piece i).verts} ×
    {Q : Finset V // Q ∈ (D.piece i).boundary.powerset})

def witnessKey : D.WitnessIndex → V :=
  Sum.elim id (fun p => p.2.1.val)

open Classical in
noncomputable def witnessSupport : D.WitnessIndex → V → Finset V :=
  Sum.elim (fun u x => {u, x}) (fun p _ => p.2.2.val)

/-- A neighbour in `H` of the opposite colour, or a piece that forces `x` under every
colouring agreeing with `c` on a certifying set inside `H`. -/
def Witness (H : Set V) : D.WitnessIndex → V → (V → Bool) → Prop :=
  Sum.elim (fun u x c => G.Adj x u ∧ u ∈ H ∧ c u ≠ c x)
    (fun p x c => (p.2.2.val : Set V) ⊆ H ∧
      (D.piece p.1).UniversalAt (p.2.2.val : Set V) c x)

theorem witness_local (H : Set V) (j : D.WitnessIndex) (x : V) (c c' : V → Bool)
    (h : Set.EqOn c c' (D.witnessSupport j x)) (hW : D.Witness H j x c) :
    D.Witness H j x c' := by
  classical
  rcases j with u | p
  · obtain ⟨hadj, huH, hne⟩ := hW
    have hu : c u = c' u := h (by simp [witnessSupport])
    have hx : c x = c' x := h (by simp [witnessSupport])
    exact ⟨hadj, huH, fun heq => hne (hu.trans (heq.trans hx.symm))⟩
  · obtain ⟨hQ, hU⟩ := hW
    exact ⟨hQ, fun c₁ hc₁ => hU c₁ fun y hy => (hc₁ hy).trans (h hy).symm⟩

theorem witness_of_eqOn (H : Set V) (c d : V → Bool) (h : Set.EqOn c d H) (x : V)
    (hx : x ∈ H) (j : D.WitnessIndex) (hW : D.Witness H j x c) : D.Witness H j x d := by
  rcases j with u | p
  · obtain ⟨hadj, huH, hne⟩ := hW
    exact ⟨hadj, huH, fun heq => hne ((h huH).trans (heq.trans (h hx).symm))⟩
  · obtain ⟨hQ, hU⟩ := hW
    exact ⟨hQ, fun c₁ hc₁ => hU c₁ fun y hy => (hc₁ hy).trans (h (hQ hy)).symm⟩

/-- A vertex with finitely many opponents has finitely many witnesses. -/
theorem witness_finite (M H : Set V) (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M)
    (c : V → Bool) (hc : StrongMaximal G M c) (x : V)
    (hO : (oppositeSet G c x).Finite) : {j | D.Witness H j x c}.Finite := by
  classical
  have hI := D.finite_pieces_meeting hO
  have hT : ((Sum.inl : V → D.WitnessIndex) '' oppositeSet G c x ∪
      ⋃ i ∈ {i | ∃ w ∈ oppositeSet G c x, w ∈ (D.piece i).verts},
        Set.range (fun t : {w : V // w ∈ (D.piece i).verts} ×
            {Q : Finset V // Q ∈ (D.piece i).boundary.powerset} =>
          (Sum.inr ⟨i, t⟩ : D.WitnessIndex))).Finite :=
    (hO.image Sum.inl).union (hI.biUnion fun i _ => Set.finite_range _)
  refine hT.subset ?_
  rintro (u | ⟨i, t⟩) hW
  · obtain ⟨hadj, _, hne⟩ := hW
    exact Or.inl ⟨u, ⟨hadj, hne⟩, rfl⟩
  · obtain ⟨_, hU⟩ := hW
    obtain ⟨z, hz, hadj, hne⟩ := (D.piece i).opponent_of_forcedAt M c
      (D.piece_subset M hM i) hc x (hU c fun _ _ => rfl)
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, ⟨z, ⟨hadj, hne⟩, hz⟩, t, rfl⟩)

/-- The vertex `x` can be given a new witness at every finite stage: the colours on
`S` and on the committed set `K` are kept, and the key avoids `F`. -/
def Servable (S H : Set V) (q : V → Bool) (x : V) : Prop :=
  ∀ (K F : Finset V) (c : V → Bool), ∃ (j : D.WitnessIndex) (c' : V → Bool),
    D.witnessKey j ∉ F ∧ Set.EqOn c' q S ∧ Set.EqOn c' c (↑K \ S) ∧ D.Witness H j x c'

/-- A robust frozen colouring extends to all of `H` when every other vertex of `H` can
always be served. -/
theorem robust_of_servable [Countable V] (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H) (hq : Robust G M S q)
    (hserve : ∀ x ∈ H, x ∉ S → D.Servable S H q x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M H q' := by
  obtain ⟨c, hcS, hc⟩ := FreshSelection.exists_fresh_selection S (H \ S) q D.witnessKey
    D.witnessSupport (D.Witness H) (D.witness_local H)
    (fun x hx K F c => hserve x hx.1 hx.2 K F c)
  refine ⟨c, hcS, fun d hd hdc x hxH => ?_⟩
  by_cases hxS : x ∈ S
  · exact hq d hd (fun y hy => (hdc (hSH hy)).trans (hcS hy)) x hxS
  · intro hO
    exact hc x ⟨hxH, hxS⟩ ((D.witness_finite M H hM d hd x hO).subset
      fun j hj => D.witness_of_eqOn H c d (fun y hy => (hdc hy).symm) x hxH j hj)

end PieceFamily
end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyFreshSupport.lean. -/
/-!
# Support conditions served by fresh witnesses

Over a maximal robust frozen colouring, three kinds of support let a vertex be
served at every finite stage:

* infinitely many neighbours in the target set;
* *piece support*: every finite set of committed vertices is either avoided by the
  boundaries of infinitely many pieces at the vertex, or contains the remaining free
  boundary of infinitely many of them. No bound on the boundary size is assumed.
  Boundaries with at most two free vertices are a special case;
* *pair support*: infinitely many pieces at the vertex whose optimized profile has a
  pair representation, for instance all pieces with at most three boundary vertices.

The resulting extension theorem keeps every colour of the given robust frozen
colouring. It is a special case of the countable unfriendly partition problem and
does not prove the unrestricted conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PieceFamily

open Energy

variable {V : Type u} {ι : Type v} {G : SimpleGraph V} (D : PieceFamily G ι)

/-- Piece support of `x` over the frozen set `S` inside `H`: for every finite set `K`,
infinitely many pieces at `x` have a boundary in `H` that either avoids `K` outside
`S ∪ {x}` or lies in `S ∪ K ∪ {x}`. -/
def PieceSupported (S H : Set V) (x : V) : Prop :=
  ∀ K : Finset V, {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
    ((∀ y ∈ (D.piece i).boundary, y ∈ K → y ∈ S ∨ y = x) ∨
      (∀ y ∈ (D.piece i).boundary, y ∈ S ∨ y ∈ K ∨ y = x))}.Infinite

/-- Infinitely many pieces at `x` with boundary in `H` have a pair representation. -/
def PairSupported (H : Set V) (x : V) : Prop :=
  {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
    ∃ (K : ℤ) (a : (D.piece i).boundary → (D.piece i).boundary → ℤ),
      PairProfile.Represents (D.piece i).profile K a}.Infinite

/-- Support by neighbours in `H`, by pieces, or by pair-profile pieces. -/
def SupportedAt (S H : Set V) (x : V) : Prop :=
  (G.neighborSet x ∩ H).Infinite ∨ D.PieceSupported S H x ∨ D.PairSupported H x

theorem PieceSupported.mono {S S' H : Set V} (hS : S ⊆ S') {x : V}
    (h : D.PieceSupported S H x) : D.PieceSupported S' H x :=
  fun K => (h K).mono fun _ hi => ⟨hi.1, hi.2.1, hi.2.2.imp
    (fun h y hyB hyK => (h y hyB hyK).imp_left fun hy => hS hy)
    (fun h y hyB => (h y hyB).imp_left fun hy => hS hy)⟩

/-- Fresh pieces: every finite set is avoided outside `S ∪ {x}`. -/
theorem pieceSupported_of_fresh (S H : Set V) (x : V)
    (h : ∀ K : Finset V, {i | x ∈ (D.piece i).boundary ∧
      ((D.piece i).boundary : Set V) ⊆ H ∧
        ∀ y ∈ (D.piece i).boundary, y ∈ K → y ∈ S ∨ y = x}.Infinite) :
    D.PieceSupported S H x :=
  fun K => (h K).mono fun _ hi => ⟨hi.1, hi.2.1, Or.inl hi.2.2⟩

open Classical in
/-- Pieces with at most two boundary vertices outside the frozen set. -/
theorem pieceSupported_of_residual_le_two (S H : Set V) (x : V) (hxS : x ∉ S)
    (h : {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
      ((D.piece i).boundary.filter (· ∉ S)).card ≤ 2}.Infinite) :
    D.PieceSupported S H x := by
  intro K
  refine h.mono fun i hi => ?_
  obtain ⟨hxB, hBH, hcard⟩ := hi
  refine ⟨hxB, hBH, ?_⟩
  have hxR : x ∈ (D.piece i).boundary.filter (· ∉ S) := Finset.mem_filter.mpr ⟨hxB, hxS⟩
  have hone : (((D.piece i).boundary.filter (· ∉ S)).erase x).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hxR]
    omega
  by_cases hK : ∃ u ∈ ((D.piece i).boundary.filter (· ∉ S)).erase x, u ∈ K
  · obtain ⟨u, hu, huK⟩ := hK
    refine Or.inr fun y hyB => ?_
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · by_cases hyx : y = x
      · exact Or.inr (Or.inr hyx)
      · have hy : y ∈ ((D.piece i).boundary.filter (· ∉ S)).erase x :=
          Finset.mem_erase.mpr ⟨hyx, Finset.mem_filter.mpr ⟨hyB, hyS⟩⟩
        have hyu : y = u := Finset.card_le_one.mp hone y hy u hu
        exact Or.inr (Or.inl (hyu ▸ huK))
  · refine Or.inl fun y hyB hyK => ?_
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · refine Or.inr (Classical.byContradiction fun hyx => hK ⟨y, ?_, hyK⟩)
      exact Finset.mem_erase.mpr ⟨hyx, Finset.mem_filter.mpr ⟨hyB, hyS⟩⟩

/-- Pieces with at most three boundary vertices have pair representations. -/
theorem pairSupported_of_card_le_three (H : Set V) (x : V)
    (h : {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
      (D.piece i).boundary.card ≤ 3}.Infinite) : D.PairSupported H x :=
  h.mono fun i hi => ⟨hi.1, hi.2.1, (D.piece i).exists_pair_representation hi.2.2⟩

/-! ### Consequences of maximality -/

private theorem frozen_neighbors_finite (M S H : Set V) (q : V → Bool) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x : V) (hxH : x ∈ H)
    (hxS : x ∉ S) : (G.neighborSet x ∩ S).Finite := by
  by_contra hinf
  obtain ⟨q', hq'q, hq'⟩ := Robust.extend_frozen_neighbors G M S q hq x hxS hinf
  exact hxS (hmax (S ∪ {x}) q' (Set.union_subset hSH (Set.singleton_subset_iff.mpr hxH))
    hq' Set.subset_union_left hq'q (Or.inr rfl))

open Classical in
private theorem universal_finite (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x : V) (hxH : x ∈ H)
    (hxS : x ∉ S) (β : Bool) :
    {i | (D.piece i).UniversalAt (S ∪ {x}) (Function.update q x β) x}.Finite := by
  by_contra hinf
  have hr := D.robust_update_of_universal M S q hM hq x hxS β hinf
  exact hxS (hmax (S ∪ {x}) (Function.update q x β)
    (Set.union_subset hSH (Set.singleton_subset_iff.mpr hxH)) hr Set.subset_union_left
    (fun y hy => Function.update_of_ne (fun h : y = x => hxS (h ▸ hy)) _ _) (Or.inr rfl))

open Classical in
private theorem block_finite (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hH : H ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q)
    (A : Finset V) (hA : A.Nonempty) :
    {i | ((D.piece i).boundary : Set V) ⊆ H ∧
      (D.piece i).boundary.filter (· ∉ S) = A}.Finite := by
  by_contra hinf
  have hinf' : {i | ((D.piece i).boundary : Set V) ⊆ H ∧
      (D.piece i).boundary.filter (· ∉ S) = A}.Infinite := hinf
  obtain ⟨i, hiH, hiA⟩ := hinf'.nonempty
  have hAB : ∀ v ∈ A, v ∈ (D.piece i).boundary ∧ v ∉ S := by
    intro v hv
    rw [← hiA] at hv
    exact Finset.mem_filter.mp hv
  obtain ⟨a, ha⟩ := hA
  obtain ⟨q', hq'q, hq'⟩ := Robust.extend_block G M S q hq A (fun v hv => (hAB v hv).2)
    (fun v hv => hH (hiH (Finset.mem_coe.mpr (hAB v hv).1))) hM
    (D.recurrentBlock_of_infinite S A (hinf'.mono fun _ hi => hi.2))
  exact (hAB a ha).2 (hmax (S ∪ (A : Set V)) q'
    (Set.union_subset hSH fun v hv =>
      hiH (Finset.mem_coe.mpr (hAB v (Finset.mem_coe.mp hv)).1))
    hq' Set.subset_union_left hq'q (Or.inr (Finset.mem_coe.mpr ha)))

private theorem pair_finite (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x p : V)
    (hxH : x ∈ H) (hpH : p ∈ H) (hxS : x ∉ S) (hpS : p ∉ S) (hxp : x ≠ p) :
    {i | ∃ (K : ℤ) (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
      (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
      PairProfile.Represents (D.piece i).profile K a ∧ a ⟨x, hx⟩ ⟨p, hp⟩ ≠ 0}.Finite := by
  by_contra hinf
  obtain ⟨q', hq'q, hq'⟩ := D.exists_robust_of_pair M S q hM hq x p hxS hpS hxp hinf
  have hsub : S ∪ {x, p} ⊆ H := by
    rintro y (hy | hy | hy)
    · exact hSH hy
    · exact (show y = x from hy) ▸ hxH
    · exact (show y = p from hy) ▸ hpH
  exact hxS (hmax (S ∪ {x, p}) q' hsub hq' Set.subset_union_left hq'q (Or.inr (Or.inl rfl)))

private theorem favoured_choice (a : ℤ) (ha : a ≠ 0) (b : Bool) :
    PairProfile.Favoured a b (if 0 < a then !b else b) := by
  by_cases hpos : 0 < a
  · rw [if_pos hpos]
    exact Or.inl ⟨hpos, by cases b <;> decide⟩
  · rw [if_neg hpos]
    exact Or.inr ⟨lt_of_le_of_ne (not_lt.mp hpos) ha, rfl⟩

private theorem favoured_choice' (a : ℤ) (ha : a ≠ 0) (b : Bool) :
    PairProfile.Favoured a (if 0 < a then !b else b) b := by
  by_cases hpos : 0 < a
  · rw [if_pos hpos]
    exact Or.inl ⟨hpos, by cases b <;> decide⟩
  · rw [if_neg hpos]
    exact Or.inr ⟨lt_of_le_of_ne (not_lt.mp hpos) ha, rfl⟩

/-! ### Serving the remaining vertices -/

private theorem servable_of_hub (M S H : Set V) (q : V → Bool) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x : V) (hxH : x ∈ H)
    (hxS : x ∉ S) (hhub : (G.neighborSet x ∩ H).Infinite) : D.Servable S H q x := by
  classical
  intro K F c
  let cf : V → Bool := fun y => if y ∈ S then q y else c y
  have hcfS : Set.EqOn cf q S := fun y hy => if_pos hy
  have hcfc : ∀ y, y ∉ S → cf y = c y := fun y hy => if_neg hy
  have hfin := frozen_neighbors_finite M S H q hSH hq hmax x hxH hxS
  obtain ⟨u, ⟨hadj, huH⟩, hunot⟩ :=
    (hhub.sdiff (hfin.union (K ∪ F).finite_toSet)).nonempty
  have huS : u ∉ S := fun h => hunot (Or.inl ⟨hadj, h⟩)
  have huK : u ∉ K :=
    fun h => hunot (Or.inr (Finset.mem_coe.mpr (Finset.mem_union_left _ h)))
  have huF : u ∉ F :=
    fun h => hunot (Or.inr (Finset.mem_coe.mpr (Finset.mem_union_right _ h)))
  have hadj' : G.Adj x u := hadj
  have hxu : x ≠ u := G.ne_of_adj hadj'
  refine ⟨Sum.inl u, Function.update cf u (!cf x), huF, ?_, ?_, ?_⟩
  · intro y hy
    exact (Function.update_of_ne (fun h : y = u => huS (h ▸ hy)) _ _).trans (hcfS hy)
  · intro y hy
    exact (Function.update_of_ne
      (fun h : y = u => huK (h ▸ Finset.mem_coe.mp hy.1)) _ _).trans (hcfc y hy.2)
  · show G.Adj x u ∧ u ∈ H ∧
      Function.update cf u (!cf x) u ≠ Function.update cf u (!cf x) x
    refine ⟨hadj', huH, ?_⟩
    rw [Function.update_self, Function.update_of_ne hxu]
    cases cf x <;> decide

private theorem servable_of_pieceSupported (M S₀ S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hS₀ : S₀ ⊆ S) (hSH : S ⊆ H)
    (hH : H ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x : V) (hxH : x ∈ H)
    (hxS : x ∉ S) (hpiece : D.PieceSupported S₀ H x) : D.Servable S H q x := by
  classical
  intro K F c
  let cf : V → Bool := fun y => if y ∈ S then q y else c y
  have hcfS : Set.EqOn cf q S := fun y hy => if_pos hy
  have hcfc : ∀ y, y ∉ S → cf y = c y := fun y hy => if_neg hy
  -- Only finitely many pieces at `x` have their free boundary inside `K ∪ {x}`.
  have h1 : {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
      ∀ y ∈ (D.piece i).boundary, y ∈ S₀ ∨ y ∈ K ∨ y = x}.Finite := by
    have hU : (⋃ A ∈ ((insert x K).powerset : Set (Finset V)),
        {i | x ∈ (D.piece i).boundary ∧ ((D.piece i).boundary : Set V) ⊆ H ∧
          (D.piece i).boundary.filter (· ∉ S) = A}).Finite := by
      refine Set.Finite.biUnion (Finset.finite_toSet _) fun A _ => ?_
      by_cases hxA : x ∈ A
      · exact (D.block_finite M S H q hM hSH hH hq hmax A ⟨x, hxA⟩).subset
          fun i hi => ⟨hi.2.1, hi.2.2⟩
      · refine Set.Finite.subset Set.finite_empty fun i hi => hxA ?_
        rw [← hi.2.2]
        exact Finset.mem_filter.mpr ⟨hi.1, hxS⟩
    refine hU.subset fun i hi => ?_
    obtain ⟨hxB, hBH, hres⟩ := hi
    refine Set.mem_iUnion₂.mpr ⟨(D.piece i).boundary.filter (· ∉ S), ?_, hxB, hBH, rfl⟩
    refine Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun y hy => ?_)
    obtain ⟨hyB, hyS⟩ := Finset.mem_filter.mp hy
    rcases hres y hyB with hyS₀ | hyK | hyx
    · exact (hyS (hS₀ hyS₀)).elim
    · exact Finset.mem_insert_of_mem hyK
    · exact hyx ▸ Finset.mem_insert_self x K
  have h2 := D.finite_pieces_meeting F.finite_toSet
  have h3 := D.universal_finite M S H q hM hSH hq hmax x hxH hxS (!cf x)
  obtain ⟨i, ⟨hxB, hBH, hkind⟩, hnot⟩ :=
    ((hpiece K).sdiff ((h1.union h2).union h3)).nonempty
  have hfirst : ∀ y ∈ (D.piece i).boundary, y ∈ K → y ∈ S₀ ∨ y = x :=
    hkind.resolve_right fun h => hnot (Or.inl (Or.inl ⟨hxB, hBH, h⟩))
  have hF : ∀ w ∈ (D.piece i).verts, w ∉ F :=
    fun w hw hwF => hnot (Or.inl (Or.inr ⟨w, Finset.mem_coe.mpr hwF, hw⟩))
  have hnu : ¬ (D.piece i).UniversalAt (S ∪ {x}) (Function.update q x (!cf x)) x :=
    fun h => hnot (Or.inr h)
  -- Since the opposite colour is not universal, the present colour can be served.
  obtain ⟨c₁, hc₁, hforced⟩ : ∃ c₁ : V → Bool, Set.EqOn c₁ cf (S ∪ {x}) ∧
      (D.piece i).ForcedAt c₁ x := by
    rcases (D.piece i).servable_or_universal S cf x hxS hxB with h | h
    · exact h
    · refine (hnu ((D.piece i).universalAt_mono Set.Subset.rfl ?_ x h)).elim
      intro y hy
      rcases hy with hyS | hyx
      · have hne : y ≠ x := fun e => hxS (e ▸ hyS)
        rw [Function.update_of_ne hne, Function.update_of_ne hne]
        exact (hcfS hyS).symm
      · have hyx' : y = x := hyx
        rw [hyx', Function.update_self, Function.update_self]
  obtain ⟨w, hw, -⟩ := (D.piece i).boundary_touch ⟨x, hxB⟩
  let c' : V → Bool := fun y => if y ∈ (D.piece i).boundary then c₁ y else cf y
  refine ⟨Sum.inr ⟨i, ⟨w, hw⟩, ⟨(D.piece i).boundary,
    Finset.mem_powerset.mpr (Finset.Subset.refl _)⟩⟩, c', hF w hw, ?_, ?_, ?_⟩
  · intro y hy
    by_cases hyB : y ∈ (D.piece i).boundary
    · exact (if_pos hyB).trans ((hc₁ (Or.inl hy)).trans (hcfS hy))
    · exact (if_neg hyB).trans (hcfS hy)
  · intro y hy
    by_cases hyB : y ∈ (D.piece i).boundary
    · rcases hfirst y hyB (Finset.mem_coe.mp hy.1) with hyS₀ | hyx
      · exact (hy.2 (hS₀ hyS₀)).elim
      · exact (if_pos hyB).trans ((hc₁ (Or.inr hyx)).trans (hcfc y hy.2))
    · exact (if_neg hyB).trans (hcfc y hy.2)
  · show ((D.piece i).boundary : Set V) ⊆ H ∧
      (D.piece i).UniversalAt ((D.piece i).boundary : Set V) c' x
    refine ⟨hBH, fun c₂ hc₂ => ?_⟩
    exact (D.piece i).forcedAt_congr c₁ c₂
      (fun y hy => ((hc₂ hy).trans (if_pos (Finset.mem_coe.mp hy))).symm) x hforced

private theorem servable_of_pairSupported (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hq : Robust G M S q) (hmax : MaximalRobust G M S H q) (x : V) (hxH : x ∈ H)
    (hxS : x ∉ S) (hpair : D.PairSupported H x) : D.Servable S H q x := by
  classical
  intro K F c
  let cf : V → Bool := fun y => if y ∈ S then q y else c y
  have hcfS : Set.EqOn cf q S := fun y hy => if_pos hy
  have hcfc : ∀ y, y ∉ S → cf y = c y := fun y hy => if_neg hy
  have h1 := (D.universal_finite M S H q hM hSH hq hmax x hxH hxS true).union
    (D.universal_finite M S H q hM hSH hq hmax x hxH hxS false)
  have h2 := D.finite_pieces_meeting F.finite_toSet
  -- Only finitely many pieces join `x` to a committed free vertex by a nonzero term.
  have h3 : (⋃ p ∈ (K : Set V), {i | p ∈ H ∧ p ∉ S ∧ x ≠ p ∧
      ∃ (K' : ℤ) (a : (D.piece i).boundary → (D.piece i).boundary → ℤ)
        (hx : x ∈ (D.piece i).boundary) (hp : p ∈ (D.piece i).boundary),
        PairProfile.Represents (D.piece i).profile K' a ∧ a ⟨x, hx⟩ ⟨p, hp⟩ ≠ 0}).Finite := by
    refine Set.Finite.biUnion K.finite_toSet fun p _ => ?_
    by_cases hp : p ∈ H ∧ p ∉ S ∧ x ≠ p
    · exact (D.pair_finite M S H q hM hSH hq hmax x p hxH hp.1 hxS hp.2.1 hp.2.2).subset
        fun i hi => hi.2.2.2
    · exact Set.Finite.subset Set.finite_empty fun i hi => hp ⟨hi.1, hi.2.1, hi.2.2.1⟩
  obtain ⟨i, ⟨hxB, hBH, K', a, hrep⟩, hnot⟩ :=
    (hpair.sdiff ((h1.union h2).union h3)).nonempty
  have hF : ∀ w ∈ (D.piece i).verts, w ∉ F :=
    fun w hw hwF => hnot (Or.inl (Or.inr ⟨w, Finset.mem_coe.mpr hwF, hw⟩))
  have hnu : ∀ β : Bool,
      ¬ (D.piece i).UniversalAt (S ∪ {x}) (Function.update q x β) x := by
    intro β h
    cases β
    · exact hnot (Or.inl (Or.inl (Or.inr h)))
    · exact hnot (Or.inl (Or.inl (Or.inl h)))
  -- No slack: some interaction at `x` is nonzero.
  have hns : ¬ PairProfile.weight a ⟨x, hxB⟩ < 2 * pieceDegree (D.piece i).edges x :=
    fun hslack => hnu true fun c₁ _ =>
      ⟨hxB, (D.piece i).forced_of_slack K' a hrep (fun y => c₁ y.val) ⟨x, hxB⟩ hslack⟩
  obtain ⟨u, hvu, hne⟩ :=
    (D.piece i).exists_interaction_of_not_slack K' a hrep ⟨x, hxB⟩ hns
  have hxu : x ≠ u.val := fun h => hvu (Subtype.ext h)
  have huH : u.val ∈ H := hBH (Finset.mem_coe.mpr u.property)
  -- A frozen partner would force `x` universally with one colour.
  have huS : u.val ∉ S := by
    intro huS
    refine hnu (if 0 < a ⟨x, hxB⟩ u then !q u.val else q u.val) fun c₁ hc₁ => ⟨hxB, ?_⟩
    apply (D.piece i).forced_of_favoured K' a hrep (fun y => c₁ y.val) ⟨x, hxB⟩ u
    have e1 : c₁ x = (if 0 < a ⟨x, hxB⟩ u then !q u.val else q u.val) :=
      (hc₁ (Or.inr rfl)).trans (Function.update_self ..)
    have e2 : c₁ u.val = q u.val :=
      (hc₁ (Or.inl huS)).trans (Function.update_of_ne hxu.symm _ _)
    show PairProfile.Favoured (a ⟨x, hxB⟩ u) (c₁ x) (c₁ u.val)
    rw [e1, e2]
    exact favoured_choice' _ hne _
  have huK : u.val ∉ K := fun huK => hnot (Or.inr (Set.mem_iUnion₂.mpr
    ⟨u.val, Finset.mem_coe.mpr huK, huH, huS, hxu, K', a, hxB, u.property, hrep, hne⟩))
  obtain ⟨w, hw, -⟩ := (D.piece i).boundary_touch ⟨x, hxB⟩
  have hQ : ({x, u.val} : Finset V) ∈ (D.piece i).boundary.powerset := by
    refine Finset.mem_powerset.mpr fun y hy => ?_
    rcases Finset.mem_insert.mp hy with hyx | hy
    · exact hyx ▸ hxB
    · exact (Finset.mem_singleton.mp hy) ▸ u.property
  refine ⟨Sum.inr ⟨i, ⟨w, hw⟩, ⟨{x, u.val}, hQ⟩⟩,
    Function.update cf u.val (if 0 < a ⟨x, hxB⟩ u then !cf x else cf x), hF w hw, ?_, ?_, ?_⟩
  · intro y hy
    exact (Function.update_of_ne (fun h : y = u.val => huS (h ▸ hy)) _ _).trans (hcfS hy)
  · intro y hy
    exact (Function.update_of_ne
      (fun h : y = u.val => huK (h ▸ Finset.mem_coe.mp hy.1)) _ _).trans (hcfc y hy.2)
  · show ((({x, u.val} : Finset V)) : Set V) ⊆ H ∧
      (D.piece i).UniversalAt ((({x, u.val} : Finset V)) : Set V)
        (Function.update cf u.val (if 0 < a ⟨x, hxB⟩ u then !cf x else cf x)) x
    refine ⟨fun y hy => ?_, fun c₂ hc₂ => ⟨hxB, ?_⟩⟩
    · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with hyx | hy
      · exact hyx ▸ hxH
      · exact (Finset.mem_singleton.mp hy) ▸ huH
    · apply (D.piece i).forced_of_favoured K' a hrep (fun y => c₂ y.val) ⟨x, hxB⟩ u
      have e1 : c₂ x = cf x :=
        (hc₂ (by simp)).trans (Function.update_of_ne hxu _ _)
      have e2 : c₂ u.val = (if 0 < a ⟨x, hxB⟩ u then !cf x else cf x) :=
        (hc₂ (by simp)).trans (Function.update_self ..)
      show PairProfile.Favoured (a ⟨x, hxB⟩ u) (c₂ x) (c₂ u.val)
      rw [e1, e2]
      exact favoured_choice _ hne _

/-! ### The extension theorems -/

open Classical in
/-- **Fresh-witness extension with recurrent boundaries.** A robust frozen colouring on
`S` extends to a robust colouring of `H`, keeping every colour on `S`, when each further
vertex of `H` lies in a recurrent finite boundary over `S` or is supported over `S`
together with all such recurrent vertices. -/
theorem extend_robust_of_recurrent [Countable V] (M S H R : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hH : H ⊆ {x | (G.neighborSet x).Infinite}) (hq : Robust G M S q)
    (hR : ∀ x ∈ R, ∃ B : Finset V, x ∈ B ∧ (B : Set V) ⊆ H ∧ RecurrentBlock G S B)
    (hsupport : ∀ x ∈ H, x ∉ S → x ∉ R → D.SupportedAt (S ∪ R) H x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M H q' := by
  obtain ⟨S', q', hSS', hS'H, hq'q, hrob, hmax⟩ :=
    exists_maximal_robust_extending G M H S q hSH hq
  -- Recurrent boundaries are absorbed by the maximal frozen colouring.
  have hRS' : R ⊆ S' := by
    intro x hxR
    by_contra hxS'
    obtain ⟨B, hxB, hBH, hB⟩ := hR x hxR
    have hb := RecurrentBlock.relativize G S S' hSS' B hB
    obtain ⟨q'', hq''q', hq''⟩ := Robust.extend_block G M S' q' hrob (B.filter (· ∉ S'))
      (fun y hy => (Finset.mem_filter.mp hy).2)
      (fun y hy => hH (hBH (Finset.mem_coe.mpr (Finset.mem_filter.mp hy).1))) hM hb
    exact hxS' (hmax _ q''
      (Set.union_subset hS'H fun y hy =>
        hBH (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1))
      hq'' Set.subset_union_left hq''q'
      (Or.inr (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hxB, hxS'⟩))))
  obtain ⟨q'', hq''q', hq''⟩ := D.robust_of_servable M S' H q' hM hS'H hrob
    (fun x hxH hxS' => by
      rcases hsupport x hxH (fun h => hxS' (hSS' h)) (fun h => hxS' (hRS' h)) with
        hhub | hpiece | hpair
      · exact D.servable_of_hub M S' H q' hS'H hrob hmax x hxH hxS' hhub
      · exact D.servable_of_pieceSupported M (S ∪ R) S' H q' hM
          (Set.union_subset hSS' hRS') hS'H hH hrob hmax x hxH hxS' hpiece
      · exact D.servable_of_pairSupported M S' H q' hM hS'H hrob hmax x hxH hxS' hpair)
  exact ⟨q'', fun y hy => (hq''q' (hSS' hy)).trans (hq'q hy), hq''⟩

/-- **Fresh-witness extension.** A robust frozen colouring on `S` extends to a robust
colouring of `H`, keeping every colour on `S`, when each further vertex of `H` is
supported by neighbours in `H`, by pieces, or by pair-profile pieces. -/
theorem extend_robust [Countable V] (M S H : Set V) (q : V → Bool)
    (hM : ∀ x, (G.neighborSet x).Finite → x ∈ M) (hSH : S ⊆ H)
    (hH : H ⊆ {x | (G.neighborSet x).Infinite}) (hq : Robust G M S q)
    (hsupport : ∀ x ∈ H, x ∉ S → D.SupportedAt S H x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧ Robust G M H q' :=
  D.extend_robust_of_recurrent M S H ∅ q hM hSH hH hq (fun _ hx => hx.elim)
    (fun x hxH hxS _ => by simpa only [Set.union_empty] using hsupport x hxH hxS)

/-- **Supported exhaustion.** Suppose that whenever a set `S` of infinite-degree
vertices leaves infinitely many of them outside, there is a nonempty recurrent block
over `S`, or a nonempty set `J` of further infinite-degree vertices each supported
inside `S ∪ J` over `S`. Then the countable graph has an unfriendly partition. A
vertex with infinitely many neighbours in `S`, and a set of vertices each having
infinitely many neighbours in the set, are instances of the second alternative. -/
theorem exists_unfriendly_of_supported_steps [Countable V]
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      ({v | (G.neighborSet v).Infinite} \ S).Infinite →
      (∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) ∨
      (∃ J : Set V, J.Nonempty ∧ (∀ v ∈ J, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        ∀ v ∈ J, D.SupportedAt S (S ∪ J) v)) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v := by
  obtain ⟨S, q, hSH, hrob, hmax⟩ := exists_maximal_robust G
    {v | (G.neighborSet v).Infinite}ᶜ {v | (G.neighborSet v).Infinite}
  by_cases hfin : ({v | (G.neighborSet v).Infinite} \ S).Finite
  · exact exists_unfriendly_of_robust_cofinite G S q hSH hrob hfin
  · exfalso
    rcases h S hSH hfin with ⟨A, ⟨a, ha⟩, hA, hblock⟩ | ⟨J, ⟨j, hj⟩, hJ, hJsup⟩
    · obtain ⟨q', hq'q, hq'⟩ := Robust.extend_block G _ S q hrob A
        (fun v hv => (hA v hv).2) (fun v hv => (hA v hv).1)
        (fun x hx hinf => hinf hx) hblock
      exact (hA a ha).2 (hmax (S ∪ (A : Set V)) q'
        (Set.union_subset hSH (fun v hv => (hA v hv).1)) hq' Set.subset_union_left hq'q
        (Or.inr ha))
    · have hH : S ∪ J ⊆ {v | (G.neighborSet v).Infinite} :=
        Set.union_subset hSH (fun v hv => (hJ v hv).1)
      obtain ⟨q', hq'q, hq'⟩ := D.extend_robust {v | (G.neighborSet v).Infinite}ᶜ S
        (S ∪ J) q (fun x hx hinf => hinf hx) Set.subset_union_left hH hrob
        (fun x hx hxS => hJsup x (hx.resolve_left hxS))
      exact (hJ j hj).2 (hmax (S ∪ J) q' hH hq' Set.subset_union_left hq'q (Or.inr hj))

end TenChallenges.Continuation.PieceFamily

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
    letI : Encodable V := Encodable.ofCountable V
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
  haveI : Infinite s := Set.infinite_coe_iff.mpr hs
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber (fun e : s => f e.val)
  haveI := hb
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
    haveI : Infinite Y := Set.infinite_coe_iff.mpr (hc x hxS)
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

/- Inlined from Continuation/UnfriendlyPairWitness.lean. -/
/-!
# Pair-profile witnesses without covering every finite-degree vertex

The auxiliary edge type retains each piece and each pair identity. Vertices
with infinitely many positive-slack pieces can receive arbitrary hub colours.
The two finiteness arguments use finite pieces and finite boundary-pair fibres,
without any uniform size bound or any countability assumption on the index type.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

open Energy
open scoped BigOperators

variable {V : Type u} {ι : Type v}

abbrev Hubs (G : SimpleGraph V) := {x : V // (G.neighborSet x).Infinite}

/-- Disjoint closed finite pieces with pair profiles. They need not cover the
finite-degree vertices. -/
structure PairWitnessSystem (G : SimpleGraph V) (ι : Type v) where
  piece : ι → Energy.FinitePiece G
  disjoint : Pairwise (Function.onFun Disjoint (fun i => (piece i).verts))
  boundary_hub : ∀ i, ∀ x : (piece i).boundary, (G.neighborSet x.val).Infinite
  constant : ι → ℤ
  coefficient : (i : ι) → (piece i).boundary → (piece i).boundary → ℤ
  representation : ∀ i, PairProfile.Represents (piece i).profile (constant i) (coefficient i)

namespace PairWitnessSystem

variable {G : SimpleGraph V} (D : PairWitnessSystem G ι)

abbrev DirectEdge (_D : PairWitnessSystem G ι) :=
  {p : Hubs G × Hubs G // G.Adj p.1.val p.2.val}

abbrev PiecePair (i : ι) := {p : (D.piece i).boundary × (D.piece i).boundary //
  p.1 ≠ p.2 ∧ D.coefficient i p.1 p.2 ≠ 0}

abbrev ComponentEdge := Σ i : ι, D.PiecePair i

abbrev Edge := D.DirectEdge ⊕ D.ComponentEdge

def hubOfBoundary (i : ι) (x : (D.piece i).boundary) : Hubs G :=
  ⟨x.val, D.boundary_hub i x⟩

noncomputable def auxiliary : SignedSelection.SignedMultiGraph (Hubs G) D.Edge where
  left := Sum.elim (fun e => e.val.1) (fun e => D.hubOfBoundary e.1 e.2.val.1)
  right := Sum.elim (fun e => e.val.2) (fun e => D.hubOfBoundary e.1 e.2.val.2)
  parity := Sum.elim (fun _ => true) (fun e => decide (0 < D.coefficient e.1 e.2.val.1 e.2.val.2))
  loopless := by
    intro e
    cases e with
    | inl e => exact fun h => G.ne_of_adj e.property (congrArg Subtype.val h)
    | inr e =>
      exact fun h => e.2.property.1
        (Subtype.ext (congrArg (Subtype.val : Hubs G → V) h))

def source : D.Edge → Option ι := Sum.elim (fun _ => none) (fun e => some e.1)

def automatic (x : Hubs G) : Set ι := {i | ∃ hx : x.val ∈ (D.piece i).boundary,
  PairProfile.weight (D.coefficient i) ⟨x.val, hx⟩ <
    2 * pieceDegree (D.piece i).edges x.val}

def protectedHubs : Set (Hubs G) := {x | (D.automatic x).Infinite}

private theorem piece_in_finite (i : ι) :
    ((D.piece i).verts : Set V) ⊆ {x | (G.neighborSet x).Infinite}ᶜ :=
  fun x hx hInf => hInf ((D.piece i).finite_degree x hx)

private theorem finite_pieces_meeting {S : Set V} (hS : S.Finite) :
    {i | ∃ w ∈ S, w ∈ (D.piece i).verts}.Finite := by
  have hf : ∀ w : V, {i | w ∈ (D.piece i).verts}.Subsingleton := by
    intro w i hi j hj
    by_contra hij
    exact Finset.disjoint_left.mp (D.disjoint hij) hi hj
  exact (hS.biUnion (fun w _ => (hf w).finite)).subset
    (fun i ⟨w, hw, hwi⟩ => Set.mem_iUnion₂.mpr ⟨w, hw, hwi⟩)

private theorem automatic_forces (x : Hubs G) (i : ι) (hi : i ∈ D.automatic x)
    (c : V → Bool) (hc : StrongMaximal G {x | (G.neighborSet x).Infinite}ᶜ c) :
    ∃ w ∈ (D.piece i).verts, G.Adj x.val w ∧ c w ≠ c x.val := by
  obtain ⟨hx, hslack⟩ := hi
  exact (D.piece i).opponent_of_slack _ c (D.piece_in_finite i) hc
    (fun v => c v.val) (fun _ => rfl) (D.constant i) (D.coefficient i)
    (D.representation i) ⟨x.val, hx⟩ hslack

/-- A hub has infinitely many direct hub neighbours or infinitely many selected
finite pieces incident with it. -/
def SupportedAt (x : Hubs G) : Prop :=
  (G.neighborSet x.val ∩ {y | (G.neighborSet y).Infinite}).Infinite ∨
    {i | x.val ∈ (D.piece i).boundary}.Infinite

private theorem auxiliary_degree (x : Hubs G) (hx : x ∉ D.protectedHubs)
    (hsupport : D.SupportedAt x) : {e | D.auxiliary.Incident x e}.Infinite := by
  classical
  intro hfin
  have hAuto : (D.automatic x).Finite := Set.not_infinite.mp hx
  let incident : Set D.Edge := {e | D.auxiliary.Incident x e}
  let sources : Set ι := {i | some i ∈ D.source '' incident}
  have hSource : sources.Finite :=
    (hfin.image D.source).preimage (fun _ _ _ _ h => Option.some.inj h)
  let J : Set ι := D.automatic x ∪ sources
  have hJ : J.Finite := hAuto.union hSource
  let H : Set V :=
    (fun e : D.Edge => (D.auxiliary.left e).val) '' incident ∪
      (fun e : D.Edge => (D.auxiliary.right e).val) '' incident
  have hH : H.Finite :=
    (hfin.image (fun e => (D.auxiliary.left e).val)).union
      (hfin.image (fun e => (D.auxiliary.right e).val))
  rcases hsupport with hHub | hPiece
  · apply hHub (hH.subset ?_)
    intro w hw
    let e : D.Edge := Sum.inl ⟨(x, ⟨w, hw.2⟩), hw.1⟩
    exact Or.inr ⟨e, Or.inl rfl, rfl⟩
  · apply hPiece (hJ.subset ?_)
    intro i hxB
    let v : (D.piece i).boundary := ⟨x.val, hxB⟩
    by_cases hslack : PairProfile.weight (D.coefficient i) v <
        2 * pieceDegree (D.piece i).edges x.val
    · exact Or.inl ⟨hxB, hslack⟩
    · obtain ⟨u, hvu, hne⟩ := (D.piece i).exists_interaction_of_not_slack
        (D.constant i) (D.coefficient i) (D.representation i) v hslack
      let e : D.Edge := Sum.inr ⟨i, ⟨(v, u), hvu, hne⟩⟩
      have he : D.auxiliary.Incident x e := Or.inl rfl
      exact Or.inr ⟨e, he, rfl⟩

private theorem favoured_of_signed (a : ℤ) (ha : a ≠ 0) (x y : Bool)
    (h : x = SignedSelection.twist y (decide (0 < a))) :
    PairProfile.Favoured a x y := by
  by_cases hp : 0 < a
  · refine Or.inl ⟨hp, ?_⟩
    cases x <;> cases y <;> simp_all [SignedSelection.twist]
  · have hn : a < 0 := by omega
    refine Or.inr ⟨hn, ?_⟩
    simpa only [hp, decide_false, SignedSelection.twist, Bool.false_eq_true, if_false] using h

private theorem component_forces (x : Hubs G) (h : Hubs G → Bool) (c : V → Bool)
    (hc : StrongMaximal G {x | (G.neighborSet x).Infinite}ᶜ c)
    (hmatch : ∀ y : Hubs G, c y.val = h y) (e : D.ComponentEdge)
    (hi : D.auxiliary.Incident x (Sum.inr e))
    (hs : D.auxiliary.Satisfied h (Sum.inr e)) :
    ∃ w ∈ (D.piece e.1).verts, G.Adj x.val w ∧ c w ≠ c x.val := by
  let i := e.1
  let u := e.2.val.1
  let v := e.2.val.2
  change h (D.hubOfBoundary i u) =
    SignedSelection.twist (h (D.hubOfBoundary i v)) (decide (0 < D.coefficient i u v)) at hs
  rw [← hmatch (D.hubOfBoundary i u), ← hmatch (D.hubOfBoundary i v)] at hs
  have hf := favoured_of_signed (D.coefficient i u v) e.2.property.2
    (c u.val) (c v.val) hs
  have hrev : PairProfile.Favoured (D.coefficient i v u) (c v.val) (c u.val) := by
    rw [(D.representation i).1 v u]
    exact hf.elim (fun h => Or.inl ⟨h.1, h.2.symm⟩) (fun h => Or.inr ⟨h.1, h.2.symm⟩)
  have hforce : ∀ z t : (D.piece i).boundary,
      PairProfile.Favoured (D.coefficient i z t) (c z.val) (c t.val) →
      ∃ w ∈ (D.piece i).verts, G.Adj z.val w ∧ c w ≠ c z.val :=
    fun z t hf => (D.piece i).opponent_of_favoured _ c (D.piece_in_finite i) hc
      (fun y => c y.val) (fun _ => rfl) (D.constant i) (D.coefficient i)
      (D.representation i) z t hf
  change D.hubOfBoundary i u = x ∨ D.hubOfBoundary i v = x at hi
  rcases hi with hu | hv
  · obtain ⟨w, hw, hadj, hne⟩ := hforce u v hf
    exact ⟨w, hw, (congrArg (Subtype.val : Hubs G → V) hu) ▸ hadj,
      (congrArg (Subtype.val : Hubs G → V) hu) ▸ hne⟩
  · obtain ⟨w, hw, hadj, hne⟩ := hforce v u hrev
    exact ⟨w, hw, (congrArg (Subtype.val : Hubs G → V) hv) ▸ hadj,
      (congrArg (Subtype.val : Hubs G → V) hv) ▸ hne⟩

private theorem direct_forces (x : Hubs G) (h : Hubs G → Bool) (c : V → Bool)
    (hmatch : ∀ y : Hubs G, c y.val = h y) (e : D.DirectEdge)
    (hi : D.auxiliary.Incident x (Sum.inl e))
    (hs : D.auxiliary.Satisfied h (Sum.inl e)) :
    (e.val.1 = x ∧ e.val.2.val ∈ oppositeSet G c x.val) ∨
      (e.val.2 = x ∧ e.val.1.val ∈ oppositeSet G c x.val) := by
  change h e.val.1 = SignedSelection.twist (h e.val.2) true at hs
  have hne : c e.val.1.val ≠ c e.val.2.val := by
    rw [hmatch e.val.1, hmatch e.val.2]
    cases h₁ : h e.val.1 <;> cases h₂ : h e.val.2 <;>
      simp_all [SignedSelection.twist]
  change e.val.1 = x ∨ e.val.2 = x at hi
  rcases hi with rfl | rfl
  · exact Or.inl ⟨rfl, e.property, hne.symm⟩
  · exact Or.inr ⟨rfl, e.property.symm, hne⟩

private theorem satisfied_finite (x : Hubs G) (h : Hubs G → Bool) (c : V → Bool)
    (hc : StrongMaximal G {x | (G.neighborSet x).Infinite}ᶜ c)
    (hmatch : ∀ y : Hubs G, c y.val = h y)
    (hO : (oppositeSet G c x.val).Finite) :
    {e | D.auxiliary.Incident x e ∧ D.auxiliary.Satisfied h e}.Finite := by
  classical
  let O : Set V := oppositeSet G c x.val
  have hOI : {y : Hubs G | y.val ∈ O}.Finite :=
    hO.preimage (fun _ _ _ _ h => Subtype.ext h)
  let A : Set (Hubs G × Hubs G) :=
    (fun y => (x, y)) '' {y : Hubs G | y.val ∈ O} ∪
      (fun y => (y, x)) '' {y : Hubs G | y.val ∈ O}
  have hA : A.Finite :=
    (hOI.image (fun y => (x, y))).union (hOI.image (fun y => (y, x)))
  have hD : {e : D.DirectEdge | e.val ∈ A}.Finite :=
    hA.preimage (fun _ _ _ _ h => Subtype.ext h)
  let J : Set ι := {i | ∃ w ∈ O, w ∈ (D.piece i).verts}
  have hJ : J.Finite := D.finite_pieces_meeting hO
  have hT : ((Sum.inl : D.DirectEdge → D.Edge) '' {e : D.DirectEdge | e.val ∈ A} ∪
      ⋃ i ∈ J, Set.range (fun p : D.PiecePair i =>
        (Sum.inr ⟨i, p⟩ : D.Edge))).Finite :=
    (hD.image Sum.inl).union (hJ.biUnion fun i _ =>
      Set.finite_range (fun p : D.PiecePair i => (Sum.inr ⟨i, p⟩ : D.Edge)))
  refine hT.subset ?_
  rintro (e | e) ⟨hi, hs⟩
  · apply Or.inl
    refine ⟨e, ?_, rfl⟩
    rcases D.direct_forces x h c hmatch e hi hs with ⟨hL, hy⟩ | ⟨hR, hy⟩
    · exact Or.inl ⟨e.val.2, hy, Prod.ext hL.symm rfl⟩
    · exact Or.inr ⟨e.val.1, hy, Prod.ext rfl hR.symm⟩
  · obtain ⟨w, hw, hadj, hne⟩ := D.component_forces x h c hc hmatch e hi hs
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨e.1, ⟨w, ⟨hadj, hne⟩, hw⟩, e.2, rfl⟩)

/-- A robust hub reservoir may keep its colours while the remaining hubs are
supported by selected pair-profile witnesses. -/
theorem extend_robust [Countable V] (S : Set V) (q : V → Bool)
    (hS : S ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ S q)
    (hsupport : ∀ x : Hubs G, x.val ∉ S → D.SupportedAt x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧
      Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q' := by
  classical
  let P : Set (Hubs G) := {x | x.val ∈ S} ∪ D.protectedHubs
  obtain ⟨h, hfix, hh⟩ := D.auxiliary.exists_infinitely_satisfied_extension
    P (fun x => q x.val) (fun x hx => D.auxiliary_degree x
      (fun ha => hx (Or.inr ha)) (hsupport x (fun hs => hx (Or.inl hs))))
  let q' : V → Bool := fun x =>
    if hx : (G.neighborSet x).Infinite then h ⟨x, hx⟩ else q x
  have hq'S : Set.EqOn q' q S := fun x hx =>
    (dif_pos (hS hx)).trans (hfix (Or.inl hx))
  refine ⟨q', hq'S, ?_⟩
  intro c hc hcq v hv
  by_cases hvS : v ∈ S
  · exact hq c hc (fun y hy => (hcq (hS hy)).trans (hq'S hy)) v hvS
  · intro hO
    let x : Hubs G := ⟨v, hv⟩
    have hmatch : ∀ y : Hubs G, c y.val = h y := fun y =>
      (hcq y.property).trans (dif_pos y.property)
    by_cases hx : x ∈ D.protectedHubs
    · apply hx
      apply (D.finite_pieces_meeting hO).subset
      intro i hi
      obtain ⟨w, hw, hadj, hne⟩ := D.automatic_forces x i hi c hc
      exact ⟨w, ⟨hadj, hne⟩, hw⟩
    · exact hh x (fun hp => hp.elim hvS hx) (D.satisfied_finite x h c hc hmatch hO)

/-- Every strongly maximal completion of the selected hub colours is unfriendly
at every hub. Witnesses are certified uniformly over all such completions. -/
theorem exists_robust (D : PairWitnessSystem G ι) [Countable V]
    (hsupport : ∀ x : Hubs G, D.SupportedAt x) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  obtain ⟨q, _, hq⟩ := D.extend_robust ∅ (fun _ => false) (Set.empty_subset _)
    (fun _ _ _ _ hv => hv.elim) (fun x _ => hsupport x)
  exact ⟨q, hq⟩

/-- Recurrent finite boundaries of arbitrary size may supply the hubs not
supported by selected pair-profile pieces. -/
theorem exists_robust_of_recurrent_or_supported [Countable V]
    (h : ∀ x : Hubs G,
      (∃ B : Finset V, x.val ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
        RecurrentBlock G ∅ B) ∨ D.SupportedAt x) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  classical
  obtain ⟨S, q, hSH, hrob, hmax⟩ := exists_maximal_robust G
    {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite}
  have hs : ∀ x : Hubs G, x.val ∉ S → D.SupportedAt x := by
    intro x hxS
    rcases h x with ⟨B, hxB, hBI, hB⟩ | hs
    · have hb := RecurrentBlock.relativize G ∅ S (Set.empty_subset S) B hB
      obtain ⟨q', hq'q, hq'⟩ := Robust.extend_block G _ S q hrob (B.filter (· ∉ S))
        (fun y hy => (Finset.mem_filter.mp hy).2)
        (fun y hy => hBI y (Finset.mem_filter.mp hy).1)
        (fun y hy hInf => hInf hy) hb
      exact (hxS (hmax _ q'
        (Set.union_subset hSH (fun y hy => hBI y (Finset.mem_filter.mp hy).1))
        hq' Set.subset_union_left hq'q (Or.inr (Finset.mem_filter.mpr ⟨hxB, hxS⟩)))).elim
    · exact hs
  obtain ⟨q', _, hq'⟩ := D.extend_robust S q hSH hrob hs
  exact ⟨q', hq'⟩

/-- The robust hub assignment gives a global unfriendly partition. -/
theorem exists_unfriendly (D : PairWitnessSystem G ι) [Countable V]
    (hsupport : ∀ x : Hubs G, D.SupportedAt x) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨q, hq⟩ := D.exists_robust hsupport
  exact exists_unfriendly_of_robust_cofinite G {x | (G.neighborSet x).Infinite} q
    Set.Subset.rfl hq (by simp)

end PairWitnessSystem
end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyPairAssembly.lean. -/
/-!
# Covering pair-profile decompositions

A decomposition covering every finite-degree vertex supplies the support
hypothesis of `PairWitnessSystem`. Its previous public selection interfaces
remain available through that witness system.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation

open Energy

variable {V : Type u} {ι : Type v}

/-- A covering collection of disjoint closed finite pieces with pair profiles. -/
structure PairDecomposition (G : SimpleGraph V) (ι : Type v) where
  piece : ι → Energy.FinitePiece G
  disjoint : Pairwise (Function.onFun Disjoint (fun i => (piece i).verts))
  cover : ∀ x, (G.neighborSet x).Finite → ∃ i, x ∈ (piece i).verts
  boundary_hub : ∀ i, ∀ x : (piece i).boundary, (G.neighborSet x.val).Infinite
  constant : ι → ℤ
  coefficient : (i : ι) → (piece i).boundary → (piece i).boundary → ℤ
  representation : ∀ i, PairProfile.Represents (piece i).profile (constant i) (coefficient i)


namespace PairDecomposition

variable {G : SimpleGraph V} (D : PairDecomposition G ι)

/-- Forget coverage while retaining the selected pieces and their certificates. -/
def toPairWitnessSystem : PairWitnessSystem G ι where
  piece := D.piece
  disjoint := D.disjoint
  boundary_hub := D.boundary_hub
  constant := D.constant
  coefficient := D.coefficient
  representation := D.representation

abbrev DirectEdge (D : PairDecomposition G ι) := D.toPairWitnessSystem.DirectEdge
abbrev PiecePair (i : ι) := D.toPairWitnessSystem.PiecePair i
abbrev ComponentEdge := D.toPairWitnessSystem.ComponentEdge
abbrev Edge := D.toPairWitnessSystem.Edge
abbrev hubOfBoundary (i : ι) (x : (D.piece i).boundary) :=
  D.toPairWitnessSystem.hubOfBoundary i x
noncomputable abbrev auxiliary := D.toPairWitnessSystem.auxiliary
abbrev source := D.toPairWitnessSystem.source
abbrev automatic := D.toPairWitnessSystem.automatic
abbrev protectedHubs := D.toPairWitnessSystem.protectedHubs

/-- Coverage and infinite original degree force infinitely many direct hub
neighbours or infinitely many incident selected pieces. -/
theorem supportedAt (x : Hubs G) : D.toPairWitnessSystem.SupportedAt x := by
  classical
  by_cases hHub : (G.neighborSet x.val ∩ {y | (G.neighborSet y).Infinite}).Infinite
  · exact Or.inl hHub
  · refine Or.inr ?_
    intro hPiece
    have hHF := Set.not_infinite.mp hHub
    have hP : (⋃ i ∈ {i | x.val ∈ (D.piece i).boundary}, ((D.piece i).verts : Set V)).Finite :=
      hPiece.biUnion (fun i _ => (D.piece i).verts.finite_toSet)
    apply x.property ((hHF.union hP).subset ?_)
    intro w hw
    by_cases hwI : (G.neighborSet w).Infinite
    · exact Or.inl ⟨hw, hwI⟩
    · obtain ⟨i, hwi⟩ := D.cover w (Set.not_infinite.mp hwI)
      have hxC : x.val ∉ (D.piece i).verts :=
        fun h => x.property ((D.piece i).finite_degree x.val h)
      have hxB := (D.piece i).mem_boundary_of_adj hxC hwi hw
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hxB, hwi⟩)

/-- Every strongly maximal completion of the selected hub colours is unfriendly
at every hub. -/
theorem exists_robust (D : PairDecomposition G ι) [Countable V] :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q :=
  D.toPairWitnessSystem.exists_robust D.supportedAt

/-- The robust hub assignment gives a global unfriendly partition. -/
theorem exists_unfriendly (D : PairDecomposition G ι) [Countable V] :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x :=
  D.toPairWitnessSystem.exists_unfriendly D.supportedAt

end PairDecomposition
end TenChallenges.Continuation

/- Inlined from Continuation/UnfriendlyThreeBoundaryGraph.lean. -/
/-!
# Finite components with at most three boundary hubs

Every finite-degree component is finite, but there is no uniform bound on its
size. Full hub boundaries vary freely. The resulting hub assignment makes
every strongly maximal completion unfriendly, and such completions exist.
This is a special case, not a proof of the unrestricted countable conjecture.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.ThreeBoundaryGraph

open Energy

variable {V : Type u}

abbrev finiteGraph (G : SimpleGraph V) := G.induce {x | (G.neighborSet x).Finite}

abbrev Component (G : SimpleGraph V) := (finiteGraph G).ConnectedComponent

def hubBoundary (G : SimpleGraph V) (C : Component G) : Set V :=
  {x | (G.neighborSet x).Infinite ∧ ∃ y ∈ C.supp, G.Adj x y.val}

noncomputable def piece (G : SimpleGraph V) (C : Component G) (hC : C.supp.Finite) :
    FinitePiece G where
  verts := (hC.image Subtype.val).toFinset
  finite_degree := by
    intro x hx
    obtain ⟨y, _, hxy⟩ := (hC.image Subtype.val).mem_toFinset.mp hx
    exact hxy ▸ y.property

theorem piece_mem (G : SimpleGraph V) (C : Component G) (hC : C.supp.Finite) (x : V) :
    x ∈ (piece G C hC).verts ↔ ∃ y ∈ C.supp, y.val = x :=
  (hC.image Subtype.val).mem_toFinset

private theorem boundary_hub (G : SimpleGraph V) (C : Component G) (hC : C.supp.Finite)
    (x : (piece G C hC).boundary) : (G.neighborSet x.val).Infinite := by
  intro hxF
  obtain ⟨w, hw, hadj⟩ := (piece G C hC).boundary_touch x
  obtain ⟨y, hy, hyw⟩ := (piece_mem G C hC w).mp hw
  have hxy : (finiteGraph G).Adj y ⟨x.val, hxF⟩ :=
    show G.Adj y.val x.val from hyw.symm ▸ hadj.symm
  have hxC := C.mem_supp_of_adj_mem_supp hy hxy
  exact (piece G C hC).boundary_not_mem x.property
    ((piece_mem G C hC x.val).mpr ⟨⟨x.val, hxF⟩, hxC, rfl⟩)

theorem boundary_eq (G : SimpleGraph V) (C : Component G) (hC : C.supp.Finite) :
    ((piece G C hC).boundary : Set V) = hubBoundary G C := by
  refine Set.ext fun x => ⟨?_, ?_⟩
  · intro hx
    obtain ⟨w, hw, hadj⟩ := (piece G C hC).boundary_touch ⟨x, hx⟩
    obtain ⟨y, hy, hyw⟩ := (piece_mem G C hC w).mp hw
    exact ⟨boundary_hub G C hC ⟨x, hx⟩, y, hy, hyw.symm ▸ hadj⟩
  · rintro ⟨hxI, y, hy, hxy⟩
    have hyC : y.val ∈ (piece G C hC).verts :=
      (piece_mem G C hC y.val).mpr ⟨y, hy, rfl⟩
    have hxC : x ∉ (piece G C hC).verts :=
      fun h => hxI ((piece G C hC).finite_degree x h)
    exact (piece G C hC).mem_boundary_of_adj hxC hyC hxy

private theorem component_disjoint (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) :
    Pairwise (Function.onFun Disjoint (fun C => (piece G C (hfinite C)).verts)) := by
  intro C D hCD
  apply Finset.disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨y, hy, hyx⟩ := (piece_mem G C (hfinite C) x).mp hxC
  obtain ⟨z, hz, hzx⟩ := (piece_mem G D (hfinite D) x).mp hxD
  have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
  exact hCD (SimpleGraph.ConnectedComponent.eq_of_common_vertex hy (hyz.symm ▸ hz))

private theorem component_cover (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (x : V) (hx : (G.neighborSet x).Finite) :
    ∃ C : Component G, x ∈ (piece G C (hfinite C)).verts := by
  let y : {x : V // (G.neighborSet x).Finite} := ⟨x, hx⟩
  refine ⟨(finiteGraph G).connectedComponentMk y, ?_⟩
  exact (piece_mem G _ _ x).mpr
    ⟨y, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩

private theorem exists_decomposition (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hpair : ∀ C : Component G, ∃ K a,
      PairProfile.Represents (piece G C (hfinite C)).profile K a) :
    Nonempty (PairDecomposition G (Component G)) := by
  classical
  choose K a ha using hpair
  exact ⟨{
    piece := fun C => piece G C (hfinite C)
    disjoint := component_disjoint G hfinite
    cover := component_cover G hfinite
    boundary_hub := fun C => boundary_hub G C (hfinite C)
    constant := K
    coefficient := a
    representation := ha
  }⟩

/-- Generalization to components with an integer-scaled pair representation. -/
theorem exists_robust_of_pair_components [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hpair : ∀ C : Component G, ∃ K a,
      PairProfile.Represents (piece G C (hfinite C)).profile K a) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  obtain ⟨D⟩ := exists_decomposition G hfinite hpair
  exact D.exists_robust

/-- Finite components with at most three distinct boundary hubs allow robust
hub colours, uniformly over every strongly maximal completion. -/
theorem exists_robust_of_three_boundary [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hboundary : ∀ C : Component G, (hubBoundary G C).ncard ≤ 3) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  apply exists_robust_of_pair_components G hfinite
  intro C
  apply (piece G C (hfinite C)).exists_pair_representation
  have h := hboundary C
  rw [← boundary_eq G C (hfinite C)] at h
  simpa only [Set.ncard_coe_finset] using h

private theorem completion_unfriendly [Countable V] (G : SimpleGraph V)
    (q : V → Bool)
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q)
    (c : V → Bool) (hc : StrongMaximal G {x | (G.neighborSet x).Infinite}ᶜ c)
    (heq : Set.EqOn c q {x | (G.neighborSet x).Infinite}) :
    ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  intro v
  by_cases hN : (G.neighborSet v).Finite
  · exact unfriendlyAt_of_strongMaximal G _ c hc v (fun hInf => hInf hN) hN
  · exact unfriendly_of_infinite_opposite G c v (hq c hc heq v hN)

/-- The precise robust three-boundary theorem: a hub assignment has strongly
maximal completions on the finite-degree vertices, and every such completion
is globally unfriendly. -/
theorem exists_hub_assignment [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hboundary : ∀ C : Component G, (hubBoundary G C).ncard ≤ 3) :
    ∃ h : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = h x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = h x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨q, hq⟩ := exists_robust_of_three_boundary G hfinite hboundary
  obtain ⟨c, hfix, hc⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
    {x | (G.neighborSet x).Infinite} q
  have hF : {x | (G.neighborSet x).Infinite}ᶜ = {x | (G.neighborSet x).Finite} :=
    Set.ext fun _ => Set.not_infinite
  refine ⟨fun x => q x.val, ⟨c, hF ▸ hc, fun x => hfix x.property⟩, ?_⟩
  intro d hd hmatch
  exact completion_unfriendly G q hq d (hF.symm ▸ hd)
    (fun x hx => hmatch ⟨x, hx⟩)

theorem exists_unfriendly [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hboundary : ∀ C : Component G, (hubBoundary G C).ncard ≤ 3) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨h, ⟨c, hc, hmatch⟩, hall⟩ := exists_hub_assignment G hfinite hboundary
  exact ⟨fun x => some (c x), hall c hc hmatch⟩

theorem all_clocks [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hboundary : ∀ C : Component G, (hubBoundary G C).ncard ≤ 3) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly G hfinite hboundary)

end TenChallenges.Continuation.ThreeBoundaryGraph

/- Inlined from Continuation/UnfriendlyPairWitnessGraph.lean. -/
/-!
# Selected finite components as permanent hub witnesses

Only the selected components need to be finite with at most three boundary
hubs. Other components may be infinite or have arbitrary finite boundaries.
A hub is supported when it has infinitely many hub neighbours or meets
infinitely many selected components. Recurrent full boundaries of arbitrary
size may supply the other hubs. Every conclusion retains the universal
quantifier over strongly maximal completions.

These are special cases of Challenge 10; the unrestricted conjecture remains.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.PairWitnessGraph

open Energy ThreeBoundaryGraph

variable {V : Type u}

/-- Finite components whose full boundary has at most three distinct hubs. -/
abbrev SelectedComponent (G : SimpleGraph V) :=
  {C : Component G // C.supp.Finite ∧ (hubBoundary G C).ncard ≤ 3}

noncomputable def selectedPiece (G : SimpleGraph V) (C : SelectedComponent G) :
    FinitePiece G :=
  piece G C.val C.property.1

/-- Infinite support by direct hub neighbours or by selected finite components. -/
def SupportedAt (G : SimpleGraph V) (x : V) : Prop :=
  (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).Infinite ∨
    {C : SelectedComponent G | x ∈ hubBoundary G C.val}.Infinite

private theorem selected_disjoint (G : SimpleGraph V) :
    Pairwise (Function.onFun Disjoint (fun C : SelectedComponent G =>
      (selectedPiece G C).verts)) := by
  classical
  intro C D hCD
  apply Finset.disjoint_left.mpr
  intro x hxC hxD
  obtain ⟨y, hy, hyx⟩ := (piece_mem G C.val C.property.1 x).mp hxC
  obtain ⟨z, hz, hzx⟩ := (piece_mem G D.val D.property.1 x).mp hxD
  have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
  exact hCD (Subtype.ext
    (SimpleGraph.ConnectedComponent.eq_of_common_vertex hy (hyz.symm ▸ hz)))

private theorem selected_pair (G : SimpleGraph V) (C : SelectedComponent G) :
    ∃ K a, PairProfile.Represents (selectedPiece G C).profile K a := by
  apply (selectedPiece G C).exists_pair_representation
  have h := C.property.2
  rw [← boundary_eq G C.val C.property.1] at h
  simpa only [selectedPiece, Set.ncard_coe_finset] using h

/-- The selected components form a witness system without a coverage assumption. -/
noncomputable def witnessSystem (G : SimpleGraph V) :
    PairWitnessSystem G (SelectedComponent G) := by
  classical
  choose K a ha using selected_pair G
  refine {
    piece := selectedPiece G
    disjoint := selected_disjoint G
    boundary_hub := ?_
    constant := K
    coefficient := a
    representation := ha
  }
  intro C x
  have hx : x.val ∈ hubBoundary G C.val := by
    rw [← boundary_eq G C.val C.property.1]
    exact x.property
  exact hx.1

private theorem support_transfer (G : SimpleGraph V) (x : Hubs G)
    (hx : SupportedAt G x.val) : (witnessSystem G).SupportedAt x := by
  change (G.neighborSet x.val ∩ {y | (G.neighborSet y).Infinite}).Infinite ∨
    {C : SelectedComponent G | x.val ∈ (selectedPiece G C).boundary}.Infinite
  have hmem : ∀ C : SelectedComponent G,
      x.val ∈ (piece G C.val C.property.1).boundary ↔ x.val ∈ hubBoundary G C.val :=
    fun C => Set.ext_iff.mp (boundary_eq G C.val C.property.1) x.val
  simpa only [SupportedAt, selectedPiece, hmem] using hx

/-- Every hub may use direct neighbours or selected finite components. Other
finite-degree components have no imposed size or boundary condition. -/
theorem exists_robust [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G, SupportedAt G x.val) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q :=
  (witnessSystem G).exists_robust (fun x => support_transfer G x (h x))

/-- Selected components and recurrent full boundaries of arbitrary size may
supply different hubs of the same graph. -/
theorem exists_robust_of_recurrent_or_supported [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G,
      (∃ B : Finset V, x.val ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
        RecurrentBlock G ∅ B) ∨ SupportedAt G x.val) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  apply (witnessSystem G).exists_robust_of_recurrent_or_supported
  intro x
  exact (h x).imp_right (support_transfer G x)

private theorem assignment_of_robust [Countable V] (G : SimpleGraph V)
    (q : V → Bool)
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q) :
    ∃ h : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = h x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = h x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨c, hfix, hc⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
    {x | (G.neighborSet x).Infinite} q
  have hF : {x | (G.neighborSet x).Infinite}ᶜ = {x | (G.neighborSet x).Finite} :=
    Set.ext fun _ => Set.not_infinite
  refine ⟨fun x => q x.val, ⟨c, hF ▸ hc, fun x => hfix x.property⟩, ?_⟩
  intro d hd hmatch v
  by_cases hN : (G.neighborSet v).Finite
  · exact unfriendlyAt_of_strongMaximal G {x | (G.neighborSet x).Finite} d hd v hN hN
  · exact unfriendly_of_infinite_opposite G d v
      (hq d (hF.symm ▸ hd) (fun x hx => hmatch ⟨x, hx⟩) v hN)

/-- A hub assignment has strongly maximal completions on all finite-degree
vertices, and every such completion is globally unfriendly. -/
theorem exists_hub_assignment [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G, SupportedAt G x.val) :
    ∃ h : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = h x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = h x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨q, hq⟩ := exists_robust G h
  exact assignment_of_robust G q hq

/-- The same universal completion conclusion for the mixed recurrent and
selected-component criterion. -/
theorem exists_hub_assignment_of_recurrent_or_supported [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G,
      (∃ B : Finset V, x.val ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
        RecurrentBlock G ∅ B) ∨ SupportedAt G x.val) :
    ∃ h : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = h x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = h x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨q, hq⟩ := exists_robust_of_recurrent_or_supported G h
  exact assignment_of_robust G q hq

theorem exists_unfriendly [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G, SupportedAt G x.val) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨a, ⟨c, hc, hmatch⟩, hall⟩ := exists_hub_assignment G h
  exact ⟨fun x => some (c x), hall c hc hmatch⟩

theorem exists_unfriendly_of_recurrent_or_supported [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G,
      (∃ B : Finset V, x.val ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
        RecurrentBlock G ∅ B) ∨ SupportedAt G x.val) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨a, ⟨c, hc, hmatch⟩, hall⟩ := exists_hub_assignment_of_recurrent_or_supported G h
  exact ⟨fun x => some (c x), hall c hc hmatch⟩

theorem all_clocks [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G, SupportedAt G x.val) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly G h)

theorem all_clocks_of_recurrent_or_supported [Countable V] (G : SimpleGraph V)
    (h : ∀ x : Hubs G,
      (∃ B : Finset V, x.val ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
        RecurrentBlock G ∅ B) ∨ SupportedAt G x.val) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly_of_recurrent_or_supported G h)

end TenChallenges.Continuation.PairWitnessGraph

/- Inlined from Continuation/UnfriendlyFreshWitnessGraph.lean. -/
/-!
# Finite components as fresh permanent witnesses

The witness pieces are all finite components of the graph induced on the
finite-degree vertices. Other components may be infinite. A robust frozen hub
colouring is preserved, and every other hub needs one of three supports:

* infinitely many hub neighbours;
* *component support* over the frozen set `S`: every finite set `K` of hubs is, for
  infinitely many finite components at the hub, either avoided outside `S` or large
  enough to contain the rest of the boundary. There is no bound on the number of
  boundary hubs. Components with at most two boundary hubs outside `S`, and hubs that
  share only finitely many components with each other hub, are special cases;
* infinitely many finite components with at most three boundary hubs.

Every conclusion keeps the universal quantifier over strongly maximal completions.
These are special cases of Challenge 10; the unrestricted conjecture remains.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.FreshWitnessGraph

open Energy ThreeBoundaryGraph

variable {V : Type u}

/-- Finite components of the graph induced on the finite-degree vertices. -/
abbrev FiniteComponent (G : SimpleGraph V) := {C : Component G // C.supp.Finite}

/-- All finite components, as a family of pairwise disjoint finite pieces. -/
noncomputable def componentFamily (G : SimpleGraph V) :
    PieceFamily G (FiniteComponent G) where
  piece C := piece G C.val C.property
  disjoint := by
    classical
    intro C D hCD
    apply Finset.disjoint_left.mpr
    intro x hxC hxD
    obtain ⟨y, hy, hyx⟩ := (piece_mem G C.val C.property x).mp hxC
    obtain ⟨z, hz, hzx⟩ := (piece_mem G D.val D.property x).mp hxD
    have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
    exact hCD (Subtype.ext
      (SimpleGraph.ConnectedComponent.eq_of_common_vertex hy (hyz.symm ▸ hz)))

private theorem mem_boundary_iff (G : SimpleGraph V) (C : FiniteComponent G) (y : V) :
    y ∈ ((componentFamily G).piece C).boundary ↔ y ∈ hubBoundary G C.val :=
  Set.ext_iff.mp (boundary_eq G C.val C.property) y

private theorem boundary_subset_hubs (G : SimpleGraph V) (C : FiniteComponent G) :
    (((componentFamily G).piece C).boundary : Set V) ⊆ {y | (G.neighborSet y).Infinite} :=
  fun y hy => ((mem_boundary_iff G C y).mp hy).1

private theorem hubBoundary_finite (G : SimpleGraph V) (C : FiniteComponent G) :
    (hubBoundary G C.val).Finite := by
  rw [← boundary_eq G C.val C.property]
  exact Finset.finite_toSet _

/-- Component support of the hub `x` over the frozen set `S`: for every finite set `K`,
infinitely many finite components at `x` have a hub boundary that either avoids `K`
outside `S ∪ {x}` or lies in `S ∪ K ∪ {x}`. -/
def ComponentSupported (G : SimpleGraph V) (S : Set V) (x : V) : Prop :=
  ∀ K : Finset V, {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧
    ((∀ y ∈ hubBoundary G C.val, y ∈ K → y ∈ S ∨ y = x) ∨
      (∀ y ∈ hubBoundary G C.val, y ∈ S ∨ y ∈ K ∨ y = x))}.Infinite

/-- Infinitely many finite components at `x` have at most three boundary hubs. -/
def SmallBoundarySupported (G : SimpleGraph V) (x : V) : Prop :=
  {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧
    (hubBoundary G C.val).ncard ≤ 3}.Infinite

/-- The three supports of a hub outside the frozen set `S`. -/
def SupportedAt (G : SimpleGraph V) (S : Set V) (x : V) : Prop :=
  (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).Infinite ∨
    ComponentSupported G S x ∨ SmallBoundarySupported G x

/-- Fresh components: every finite set of hubs is avoided outside `S ∪ {x}`. -/
theorem componentSupported_of_fresh (G : SimpleGraph V) (S : Set V) (x : V)
    (h : ∀ K : Finset V, {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧
      ∀ y ∈ hubBoundary G C.val, y ∈ K → y ∈ S ∨ y = x}.Infinite) :
    ComponentSupported G S x :=
  fun K => (h K).mono fun _ hC => ⟨hC.1, Or.inl hC.2⟩

/-- Components with at most two boundary hubs outside the frozen set. The whole
boundary may be arbitrarily large. -/
theorem componentSupported_of_residual_le_two (G : SimpleGraph V) (S : Set V) (x : V)
    (hxS : x ∉ S)
    (h : {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧
      (hubBoundary G C.val \ S).ncard ≤ 2}.Infinite) : ComponentSupported G S x := by
  intro K
  refine h.mono fun C hC => ?_
  obtain ⟨hxB, hcard⟩ := hC
  refine ⟨hxB, ?_⟩
  have hfin : (hubBoundary G C.val \ S).Finite :=
    (hubBoundary_finite G C).subset Set.sdiff_subset
  have hthree : ∀ y u, y ∈ hubBoundary G C.val \ S → u ∈ hubBoundary G C.val \ S →
      y ≠ x → u ≠ x → y = u := by
    intro y u hy hu hyx hux
    by_contra hyu
    have hlt : 2 < (hubBoundary G C.val \ S).ncard :=
      (Set.two_lt_ncard_iff hfin).mpr
        ⟨x, y, u, ⟨hxB, hxS⟩, hy, hu, fun h => hyx h.symm, fun h => hux h.symm, hyu⟩
    omega
  by_cases hK : ∃ u ∈ hubBoundary G C.val \ S, u ≠ x ∧ u ∈ K
  · obtain ⟨u, hu, hux, huK⟩ := hK
    refine Or.inr fun y hyB => ?_
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · by_cases hyx : y = x
      · exact Or.inr (Or.inr hyx)
      · have hyu : y = u := hthree y u ⟨hyB, hyS⟩ hu hyx hux
        exact Or.inr (Or.inl (hyu ▸ huK))
  · refine Or.inl fun y hyB hyK => ?_
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · exact Or.inr (Classical.byContradiction fun hyx => hK ⟨y, ⟨hyB, hyS⟩, hyx, hyK⟩)

/-- A hub on the boundary of infinitely many finite components, sharing only finitely
many of them with each other hub outside the frozen set. -/
theorem componentSupported_of_cooccurrence (G : SimpleGraph V) (S : Set V) (x : V)
    (hinf : {C : FiniteComponent G | x ∈ hubBoundary G C.val}.Infinite)
    (hco : ∀ y, y ∉ S → y ≠ x →
      {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧ y ∈ hubBoundary G C.val}.Finite) :
    ComponentSupported G S x := by
  apply componentSupported_of_fresh
  intro K
  have hbad : (⋃ y ∈ (K : Set V), {C : FiniteComponent G | (y ∉ S ∧ y ≠ x) ∧
      x ∈ hubBoundary G C.val ∧ y ∈ hubBoundary G C.val}).Finite := by
    refine Set.Finite.biUnion K.finite_toSet fun y _ => ?_
    by_cases hy : y ∉ S ∧ y ≠ x
    · exact (hco y hy.1 hy.2).subset fun C hC => hC.2
    · exact Set.Finite.subset Set.finite_empty fun C hC => hy hC.1
  refine (hinf.sdiff hbad).mono fun C hC => ⟨hC.1, fun y hyB hyK => ?_⟩
  by_contra hno
  have hyS : y ∉ S := fun h => hno (Or.inl h)
  have hyx : y ≠ x := fun h => hno (Or.inr h)
  exact hC.2 (Set.mem_iUnion₂.mpr ⟨y, Finset.mem_coe.mpr hyK, ⟨hyS, hyx⟩, hC.1, hyB⟩)

private theorem support_transfer (G : SimpleGraph V) (S : Set V) (x : V)
    (h : SupportedAt G S x) :
    (componentFamily G).SupportedAt S {y | (G.neighborSet y).Infinite} x := by
  rcases h with hhub | hcomp | hsmall
  · exact Or.inl hhub
  · refine Or.inr (Or.inl fun K => (hcomp K).mono fun C hC => ?_)
    refine ⟨(mem_boundary_iff G C x).mpr hC.1, boundary_subset_hubs G C, ?_⟩
    exact hC.2.imp
      (fun h y hyB hyK => h y ((mem_boundary_iff G C y).mp hyB) hyK)
      (fun h y hyB => h y ((mem_boundary_iff G C y).mp hyB))
  · refine Or.inr (Or.inr ((componentFamily G).pairSupported_of_card_le_three _ x
      (hsmall.mono fun C hC => ?_)))
    refine ⟨(mem_boundary_iff G C x).mpr hC.1, boundary_subset_hubs G C, ?_⟩
    have h := hC.2
    rw [← boundary_eq G C.val C.property] at h
    have h' : (piece G C.val C.property).boundary.card ≤ 3 := by
      simpa only [Set.ncard_coe_finset] using h
    exact h'

/-- **Extension with recurrent boundaries.** A robust frozen hub colouring on `S`
extends to all hubs, keeping every colour on `S`, when each further hub lies in a
recurrent finite boundary over `S` or is supported over `S` together with all such
recurrent hubs. -/
theorem extend_robust_of_recurrent [Countable V] (G : SimpleGraph V) (S R : Set V)
    (q : V → Bool) (hS : S ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ S q)
    (hR : ∀ x ∈ R, ∃ B : Finset V, x ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
      RecurrentBlock G S B)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ S → x ∉ R → SupportedAt G (S ∪ R) x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧
      Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q' :=
  (componentFamily G).extend_robust_of_recurrent _ S _ R q (fun _ hx hInf => hInf hx) hS
    Set.Subset.rfl hq
    (fun x hx => let ⟨B, hxB, hBI, hB⟩ := hR x hx
      ⟨B, hxB, fun y hy => hBI y (Finset.mem_coe.mp hy), hB⟩)
    (fun x hxI hxS hxR => support_transfer G (S ∪ R) x (h x hxI hxS hxR))

/-- **Extension of a robust reservoir.** A robust frozen hub colouring on `S` extends
to all hubs, keeping every colour on `S`, when each further hub is supported. -/
theorem extend_robust [Countable V] (G : SimpleGraph V) (S : Set V) (q : V → Bool)
    (hS : S ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ S q)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ S → SupportedAt G S x) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧
      Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q' :=
  extend_robust_of_recurrent G S ∅ q hS hq (fun _ hx => hx.elim)
    (fun x hxI hxS _ => by simpa only [Set.union_empty] using h x hxI hxS)

/-- **Robust reservoir with two residual boundary hubs.** Each hub outside the robust
reservoir `S` has infinitely many hub neighbours or meets infinitely many finite
components with at most two boundary hubs outside `S`. The full boundaries may be
arbitrarily large and the frozen colours on them may be mixed. -/
theorem extend_robust_of_residual_le_two [Countable V] (G : SimpleGraph V) (S : Set V)
    (q : V → Bool) (hS : S ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ S q)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ S →
      (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).Infinite ∨
        {C : FiniteComponent G | x ∈ hubBoundary G C.val ∧
          (hubBoundary G C.val \ S).ncard ≤ 2}.Infinite) :
    ∃ q' : V → Bool, Set.EqOn q' q S ∧
      Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q' :=
  extend_robust G S q hS hq fun x hxI hxS => (h x hxI hxS).imp_right
    fun hres => Or.inl (componentSupported_of_residual_le_two G S x hxS hres)

/-- The hubs lying in a finite set of hubs that is the exact outside neighbourhood of
infinitely many pairwise disjoint finite pieces. -/
def recurrentHubs (G : SimpleGraph V) : Set V :=
  {x | ∃ B : Finset V, x ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
    RecurrentBlock G ∅ B}

/-- **Recurrent or supported.** Every hub lies in a recurrent finite boundary or is
supported over the set of all recurrent hubs. -/
theorem exists_robust [Countable V] (G : SimpleGraph V)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ recurrentHubs G →
      SupportedAt G (recurrentHubs G) x) :
    ∃ q : V → Bool, Robust G {x | (G.neighborSet x).Infinite}ᶜ
      {x | (G.neighborSet x).Infinite} q := by
  obtain ⟨q, -, hq⟩ := extend_robust_of_recurrent G ∅ (recurrentHubs G) (fun _ => false)
    (Set.empty_subset _) (fun _ _ _ _ hv => hv.elim) (fun _ hx => hx)
    (fun x hxI _ hxR => by simpa only [Set.empty_union] using h x hxI hxR)
  exact ⟨q, hq⟩

/-- A robust colouring of all hubs is a hub assignment with strongly maximal
completions, each of which is globally unfriendly. -/
theorem hub_assignment_of_robust [Countable V] (G : SimpleGraph V) (q : V → Bool)
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ {x | (G.neighborSet x).Infinite} q) :
    (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
      ∀ x : Hubs G, c x.val = q x.val) ∧
    ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
      (∀ x : Hubs G, c x.val = q x.val) →
      ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨c, hfix, hc⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G
    {x | (G.neighborSet x).Infinite} q
  have hF : {x | (G.neighborSet x).Infinite}ᶜ = {x | (G.neighborSet x).Finite} :=
    Set.ext fun _ => Set.not_infinite
  refine ⟨⟨c, hF ▸ hc, fun x => hfix x.property⟩, ?_⟩
  intro d hd hmatch v
  by_cases hN : (G.neighborSet v).Finite
  · exact unfriendlyAt_of_strongMaximal G {x | (G.neighborSet x).Finite} d hd v hN hN
  · exact unfriendly_of_infinite_opposite G d v
      (hq d (hF.symm ▸ hd) (fun x hx => hmatch ⟨x, hx⟩) v hN)

/-- **Universal completions over a robust reservoir.** The reservoir colours are kept,
strongly maximal completions of the resulting hub assignment exist, and every such
completion is globally unfriendly. -/
theorem exists_hub_assignment_extending [Countable V] (G : SimpleGraph V) (S R : Set V)
    (q : V → Bool) (hS : S ⊆ {x | (G.neighborSet x).Infinite})
    (hq : Robust G {x | (G.neighborSet x).Infinite}ᶜ S q)
    (hR : ∀ x ∈ R, ∃ B : Finset V, x ∈ B ∧ (∀ y ∈ B, (G.neighborSet y).Infinite) ∧
      RecurrentBlock G S B)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ S → x ∉ R → SupportedAt G (S ∪ R) x) :
    ∃ a : Hubs G → Bool, (∀ x : Hubs G, x.val ∈ S → a x = q x.val) ∧
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = a x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = a x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨q', hq'q, hq'⟩ := extend_robust_of_recurrent G S R q hS hq hR h
  obtain ⟨hex, hall⟩ := hub_assignment_of_robust G q' hq'
  exact ⟨fun x => q' x.val, fun x hx => hq'q hx, hex, hall⟩

/-- **Universal completions.** Under the recurrent-or-supported criterion, a hub
assignment has strongly maximal completions on all finite-degree vertices, and every
such completion is globally unfriendly. -/
theorem exists_hub_assignment [Countable V] (G : SimpleGraph V)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ recurrentHubs G →
      SupportedAt G (recurrentHubs G) x) :
    ∃ a : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = a x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = a x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  obtain ⟨q, hq⟩ := exists_robust G h
  obtain ⟨hex, hall⟩ := hub_assignment_of_robust G q hq
  exact ⟨fun x => q x.val, hex, hall⟩

theorem exists_unfriendly [Countable V] (G : SimpleGraph V)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ recurrentHubs G →
      SupportedAt G (recurrentHubs G) x) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨a, ⟨c, hc, hmatch⟩, hall⟩ := exists_hub_assignment G h
  exact ⟨fun x => some (c x), hall c hc hmatch⟩

theorem all_clocks [Countable V] (G : SimpleGraph V)
    (h : ∀ x, (G.neighborSet x).Infinite → x ∉ recurrentHubs G →
      SupportedAt G (recurrentHubs G) x) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly G h)

/-- **Supported exhaustion for finite components.** Whenever a set `S` of hubs leaves
infinitely many hubs outside, there is a nonempty recurrent block over `S`, or a
nonempty set `J` of further hubs each supported inside `S ∪ J` over `S` by neighbours
or finite components. Then the graph has an unfriendly partition. -/
theorem exists_unfriendly_of_supported_steps [Countable V] (G : SimpleGraph V)
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      ({v | (G.neighborSet v).Infinite} \ S).Infinite →
      (∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) ∨
      (∃ J : Set V, J.Nonempty ∧ (∀ v ∈ J, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        ∀ v ∈ J, (componentFamily G).SupportedAt S (S ∪ J) v)) :
    ∃ p : V → Option Bool, ∀ v, UnfriendlyAt G p v :=
  (componentFamily G).exists_unfriendly_of_supported_steps h

theorem all_clocks_of_supported_steps [Countable V] (G : SimpleGraph V)
    (h : ∀ S : Set V, S ⊆ {v | (G.neighborSet v).Infinite} →
      ({v | (G.neighborSet v).Infinite} \ S).Infinite →
      (∃ A : Finset V, A.Nonempty ∧ (∀ v ∈ A, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        RecurrentBlock G S A) ∨
      (∃ J : Set V, J.Nonempty ∧ (∀ v ∈ J, (G.neighborSet v).Infinite ∧ v ∉ S) ∧
        ∀ v ∈ J, (componentFamily G).SupportedAt S (S ∪ J) v)) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly_of_supported_steps G h)

/-- With every finite-degree component finite, a hub with finitely many hub neighbours
lies on the boundary of infinitely many components. -/
private theorem infinite_components_at (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite) (x : V)
    (hx : (G.neighborSet x).Infinite)
    (hhub : ¬ (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).Infinite) :
    {C : FiniteComponent G | x ∈ hubBoundary G C.val}.Infinite := by
  intro hfin
  have hHF := Set.not_infinite.mp hhub
  have hP : (⋃ C ∈ {C : FiniteComponent G | x ∈ hubBoundary G C.val},
      (((componentFamily G).piece C).verts : Set V)).Finite :=
    hfin.biUnion fun C _ => Finset.finite_toSet _
  apply hx ((hHF.union hP).subset ?_)
  intro w hw
  by_cases hwI : (G.neighborSet w).Infinite
  · exact Or.inl ⟨hw, hwI⟩
  · have hwF : (G.neighborSet w).Finite := Set.not_infinite.mp hwI
    let y : {z : V // (G.neighborSet z).Finite} := ⟨w, hwF⟩
    let C : FiniteComponent G :=
      ⟨(finiteGraph G).connectedComponentMk y, hfinite _⟩
    have hyC : y ∈ C.val.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    have hxC : x ∈ hubBoundary G C.val := ⟨hx, y, hyC, hw⟩
    have hwC : w ∈ ((componentFamily G).piece C).verts :=
      (piece_mem G C.val C.property w).mpr ⟨y, hyC, rfl⟩
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨C, hxC, Finset.mem_coe.mpr hwC⟩)

/-- **Finite co-occurrence.** Every finite-degree component is finite, with no bound on
its size or on the number of its boundary hubs, and any two hubs lie together on the
boundary of only finitely many components. Then some hub assignment has strongly
maximal completions, and every such completion is globally unfriendly. -/
theorem exists_hub_assignment_of_finite_cooccurrence [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hco : ∀ x y, (G.neighborSet x).Infinite → (G.neighborSet y).Infinite → x ≠ y →
      {C : Component G | x ∈ hubBoundary G C ∧ y ∈ hubBoundary G C}.Finite) :
    ∃ a : Hubs G → Bool,
      (∃ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c ∧
        ∀ x : Hubs G, c x.val = a x) ∧
      ∀ c : V → Bool, StrongMaximal G {x | (G.neighborSet x).Finite} c →
        (∀ x : Hubs G, c x.val = a x) →
        ∀ v, UnfriendlyAt G (fun x => some (c x)) v := by
  apply exists_hub_assignment G
  intro x hxI _
  by_cases hhub : (G.neighborSet x ∩ {y | (G.neighborSet y).Infinite}).Infinite
  · exact Or.inl hhub
  · refine Or.inr (Or.inl (componentSupported_of_cooccurrence G _ x
      (infinite_components_at G hfinite x hxI hhub) fun y _ hyx => ?_))
    by_cases hyI : (G.neighborSet y).Infinite
    · exact ((hco x y hxI hyI (Ne.symm hyx)).preimage
        Subtype.val_injective.injOn).subset fun C hC => hC
    · exact Set.Finite.subset Set.finite_empty fun C hC => hyI hC.2.1

theorem exists_unfriendly_of_finite_cooccurrence [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hco : ∀ x y, (G.neighborSet x).Infinite → (G.neighborSet y).Infinite → x ≠ y →
      {C : Component G | x ∈ hubBoundary G C ∧ y ∈ hubBoundary G C}.Finite) :
    ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x := by
  obtain ⟨a, ⟨c, hc, hmatch⟩, hall⟩ :=
    exists_hub_assignment_of_finite_cooccurrence G hfinite hco
  exact ⟨fun x => some (c x), hall c hc hmatch⟩

theorem all_clocks_of_finite_cooccurrence [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : Component G, C.supp.Finite)
    (hco : ∀ x y, (G.neighborSet x).Infinite → (G.neighborSet y).Infinite → x ≠ y →
      {C : Component G | x ∈ hubBoundary G C ∧ y ∈ hubBoundary G C}.Finite) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  all_clocks_of_global G (exists_unfriendly_of_finite_cooccurrence G hfinite hco)

end TenChallenges.Continuation.FreshWitnessGraph

theorem solution {V : Type u} [Countable V] (G : SimpleGraph V)
    (hfinite : ∀ C : (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent, C.supp.Finite)
    (hshare : ∀ x y : V, (G.neighborSet x).Infinite → (G.neighborSet y).Infinite → x ≠ y →
      {C : (G.induce {x : V | (G.neighborSet x).Finite}).ConnectedComponent |
        (∃ a ∈ C.supp, G.Adj x a.val) ∧ (∃ b ∈ C.supp, G.Adj y b.val)}.Finite)
    (r : Ordinal.{v}) : PartitionerWins G (emptyPartition V) r :=
  TenChallenges.Continuation.FreshWitnessGraph.all_clocks_of_finite_cooccurrence G hfinite
    (fun x y hx hy hxy => (hshare x y hx hy hxy).subset fun _ hC => ⟨hC.1.2, hC.2.2⟩) r

#print axioms solution
