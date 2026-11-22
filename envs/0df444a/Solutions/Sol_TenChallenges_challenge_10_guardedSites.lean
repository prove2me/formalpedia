-- Prove2me | solution 1 for TenChallenges.challenge_10_guardedSites
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:29:09.079808+00:00
-- url     : https://prove2.me/submissions/721d19e3-1925-4d3e-814e-df24c67979bd

import Definitions.Def_TenChallenges_Challenge_10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete

set_option linter.style.haveILetI false
universe u v

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

/-- Finitely supported Boolean tests with compatible finite subfamilies have a common solution. -/
theorem exists_boolean_coloring {ι : Type v} (D : Set V) (p : V → Bool)
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

/-- A finite region admits a state with no positive gain when gains add along flips. -/
theorem exists_maximal_flip_subset [DecidableEq V] {C : Type v}
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


/-! # Relative quotas from thinning -/

set_option autoImplicit false


namespace TenChallenges.Continuation

variable {V : Type u}

/-- At a vertex with at least twice its quota minus one neighbours, an unfriendly
colouring supplies the requested number of opponents. -/
theorem quota_of_unfriendly (G : SimpleGraph V) (c : V → Bool) (v : V) (q : ℕ)
    (hdeg : ((2 * q - 1 : ℕ) : ℕ∞) ≤ (G.neighborSet v).encard)
    (hUF : UnfriendlyAt G (fun w => some (c w)) v) :
    (q : ℕ∞) ≤ (Energy.oppositeSet G c v).encard := by
  obtain ⟨b, hb, hcard⟩ := hUF
  obtain rfl : b = c v := (Option.some.inj hb).symm
  exact le_of_not_gt fun hlt =>
    let same := G.neighborSet v ∩ (fun w => some (c w)) ⁻¹' {some (c v)}
    let opp := Energy.oppositeSet G c v
    let hsame : same.encard ≤ opp.encard := by
      simpa only [same, opp, Energy.oppositeSet_eq_colored, ← Set.toENat_cardinalMk, NeighColored]
        using Cardinal.enat_gc.monotone_u hcard
    let hcover : G.neighborSet v ⊆ same ∪ opp := fun w hw =>
      (eq_or_ne (c w) (c v)).elim
        (fun heq => Or.inl ⟨hw, congrArg some heq⟩)
        (fun hne => Or.inr ⟨hw, hne⟩)
    let hbound : (G.neighborSet v).encard ≤ opp.encard + opp.encard :=
      (Set.encard_le_encard hcover).trans
        ((Set.encard_union_le same opp).trans (add_le_add_left hsame _))
    let hfin : opp.Finite :=
      Set.encard_ne_top_iff.mp (hlt.trans (ENat.natCast_lt_top q)).ne
    let ⟨m, hm⟩ := hfin.exists_encard_eq_coe
    let hlt' : opp.encard < (q : ℕ∞) := hlt
    let hsmall : m < q := by
      simpa only [hm, ENat.natCast_lt_natCast] using hlt'
    let hlarge : 2 * q - 1 ≤ m + m := by
      simpa only [hm, ← Nat.cast_add, ENat.natCast_le_natCast] using hdeg.trans hbound
    by omega

end TenChallenges.Continuation

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


namespace TenChallenges.Continuation
variable {V : Type u} (G : SimpleGraph V)
theorem all_clocks_of_global
    (h : ∃ p : V → Option Bool, ∀ x, UnfriendlyAt G p x) :
    ∀ α : Ordinal.{v}, PartitionerWins G (emptyPartition V) α :=
  fun α => let ⟨p, hp⟩ := h
    partitionerWins_of_unfriendly_partition G p hp α

end TenChallenges.Continuation

set_option autoImplicit false


namespace TenChallenges.Continuation.TrianglePorts


open scoped Cardinal

variable {V : Type u}

/-- At a finite-degree vertex, enough opponents to account for half the degree suffice. -/
theorem unfriendly_of_opponent_quota (G : SimpleGraph V) (c : V → Bool) (x : V)
    (q : ℕ) (hfin : (G.neighborSet x).Finite) (hhalf : (G.neighborSet x).ncard ≤ 2 * q)
    (hopp : (q : ℕ∞) ≤ (Energy.oppositeSet G c x).encard) :
    UnfriendlyAt G (fun v => some (c v)) x := by
  let O := Energy.oppositeSet G c x
  let M := G.neighborSet x \ O
  have hsub : O ⊆ G.neighborSet x := fun _ h => h.1
  have hfinO : O.Finite := hfin.subset hsub
  have hfinM : M.Finite := hfin.sdiff
  have hcard : M.ncard + O.ncard = (G.neighborSet x).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hsub hfin
  have hcount : q ≤ O.ncard := ENat.natCast_le_natCast.mp (hfinO.cast_ncard_eq.symm ▸ hopp)
  have hM : G.neighborSet x ∩ (fun v => some (c v)) ⁻¹' {some (c x)} = M := by
    ext w
    change (G.Adj x w ∧ some (c w) = some (c x)) ↔
      G.Adj x w ∧ ¬ (G.Adj x w ∧ c w ≠ c x)
    by_cases hw : G.Adj x w <;> simp [hw]
  refine ⟨c x, rfl, ?_⟩
  simp only [NeighColored, hM, ← Energy.oppositeSet_eq_colored]
  change #M ≤ #O
  rw [← Set.cast_ncard hfinM, ← Set.cast_ncard hfinO, Nat.cast_le]
  omega

end TenChallenges.Continuation.TrianglePorts

namespace TenChallenges.Continuation.GuardedSites

variable {V : Type*}

/-- A prescribed auxiliary vertex adds one vote at each selected vertex. -/
def attach (G : SimpleGraph V) (E : Set V) : SimpleGraph (Option V) where
  Adj
    | some x, some y => G.Adj x y
    | some x, none | none, some x => x ∈ E
    | none, none => False
  symm := ⟨fun x y => by cases x <;> cases y <;> first | exact id | exact fun h => G.adj_symm h⟩
  loopless := ⟨fun x => by cases x <;> first | exact id | exact G.irrefl⟩

private theorem row_subset (G : SimpleGraph V) (E : Set V) (v : V) :
    (attach G E).neighborSet (some v) ⊆ insert none (some '' G.neighborSet v) := by
  rintro (_ | w) hw
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨w, hw, rfl⟩

private theorem same_row (G : SimpleGraph V) (E : Set V) {v : V} (hv : v ∉ E)
    (d : Option V → Bool) (h : UnfriendlyAt (attach G E) (fun w => some (d w)) (some v)) :
    UnfriendlyAt G (fun w => some (d (some w))) v := by
  classical
  let A b := NeighColored G (fun w => some (d (some w))) v b
  let B b := NeighColored (attach G E) (fun w => some (d w)) (some v) b
  let lift (b : Option Bool) (w : A b) : B b := ⟨some w.1, w.2⟩
  have inj (b) : Function.Injective (lift b) :=
    fun w z hh => Subtype.ext (Option.some.inj (congrArg Subtype.val hh))
  have onto (b) : Function.Surjective (lift b) := by
    rintro ⟨_ | w, hw⟩
    · exact (hv hw.1).elim
    · exact ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨b, hb, le⟩ := h
  have cards (t) := Cardinal.mk_congr (Equiv.ofBijective (lift t) ⟨inj t, onto t⟩)
  exact ⟨b, hb, (cards _).le.trans (le.trans (cards _).ge)⟩

private theorem biased_row (G : SimpleGraph V) (E : Set V) {v : V} (hv : v ∈ E)
    (degree : (G.neighborSet v).encard = 4) (d : Option V → Bool) (pin : d none = true)
    (h : UnfriendlyAt (attach G E) (fun w => some (d w)) (some v)) :
    UnfriendlyAt G (fun w => some (d (some w))) v ∧
      (d (some v) = true → 3 ≤ (Energy.oppositeSet G (d ∘ some) v).encard) := by
  classical
  let O := Energy.oppositeSet G (d ∘ some) v
  let O' := Energy.oppositeSet (attach G E) d (some v)
  have row : (attach G E).neighborSet (some v) = insert none (some '' G.neighborSet v) := by
    ext w
    cases w <;> simp [SimpleGraph.neighborSet, attach, hv]
  have inj : Function.Injective (some : V → Option V) := Option.some_injective V
  have size : ((attach G E).neighborSet (some v)).encard = 5 := by
    simp [row, Set.encard_insert_of_notMem, inj.encard_image, degree]
    decide
  have enough : (3 : ℕ∞) ≤ O'.encard :=
    quota_of_unfriendly (attach G E) d _ 3 (by rw [size]; decide) h
  have sub : O' ⊆ insert none (some '' O) := by
    rintro (_ | w) hw
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨w, hw, rfl⟩
  have bound : (3 : ℕ∞) ≤ O.encard + 1 := by
    simpa only [Set.encard_insert_of_notMem (show none ∉ some '' O by simp), inj.encard_image] using
      enough.trans (Set.encard_le_encard sub)
  have hfin : (G.neighborSet v).Finite := Set.encard_ne_top_iff.mp (degree ▸ by decide)
  have ofi : O.Finite := hfin.subset fun _ hw => hw.1
  have n : 2 ≤ O.ncard := by
    have lifted : (3 : ℕ∞) ≤ ((O.ncard + 1 : ℕ) : ℕ∞) := by
      simpa only [Nat.cast_add, Nat.cast_one, ofi.cast_ncard_eq] using bound
    exact Nat.le_of_succ_le_succ (ENat.natCast_le_natCast.mp lifted)
  refine ⟨TrianglePorts.unfriendly_of_opponent_quota G _ v 2 hfin ?_ ?_, ?_⟩
  · exact ENat.natCast_le_natCast.mp (hfin.cast_ncard_eq.trans degree).le
  · exact ofi.cast_ncard_eq ▸ (ENat.natCast_le_natCast.mpr n)
  · intro colour
    have plain : O' ⊆ some '' O := by
      rintro (_ | w) hw
      · exact (hw.2 (pin.trans colour.symm)).elim
      · exact ⟨w, hw, rfl⟩
    have hh := enough.trans (Set.encard_le_encard plain)
    simpa only [inj.encard_image] using hh

/-- A prescribed boundary, optionally with finitely many free hubs, admits an extension
preferring zero at tied degree-four vertices in the selected set. -/
theorem biased_extension [Countable V] (G : SimpleGraph V) (D E : Set V) (p : V → Bool)
    (degree : ∀ v ∈ E, (G.neighborSet v).encard = 4)
    (few : {v | v ∉ D ∧ (G.neighborSet v).Infinite}.Finite) :
    ∃ c, Set.EqOn c p D ∧ (∀ v, v ∉ D → UnfriendlyAt G (fun w => some (c w)) v) ∧
      ∀ v ∈ E, v ∉ D → c v = true → 3 ≤ (Energy.oppositeSet G c v).encard := by
  classical
  let P := insert (none : Option V) (some '' D)
  let b : Option V → Bool := fun x => x.elim true p
  have finite : {x | x ∉ P ∧ ((attach G E).neighborSet x).Infinite}.Finite := by
    refine (few.image some).subset ?_
    rintro (_ | v) ⟨hout, hinf⟩
    · exact (hout (Set.mem_insert _ _)).elim
    · refine ⟨v, ⟨fun hv => hout (Set.mem_insert_of_mem _ (Set.mem_image_of_mem some hv)), ?_⟩, rfl⟩
      exact fun hf => hinf (((hf.image some).insert none).subset (row_subset G E v))
  obtain ⟨d, fixed, uf⟩ := Energy.exists_unfriendly_extension (attach G E) P b finite
  have notMem {v : V} (hv : v ∉ D) : some v ∉ P := by simpa [P]
  have atNone : d none = true := fixed (Set.mem_insert _ _)
  refine ⟨d ∘ some, ?_, ?_, ?_⟩
  · exact fun v hv => fixed (Set.mem_insert_of_mem _ (Set.mem_image_of_mem some hv))
  · intro v hv
    exact if he : v ∈ E then (biased_row G E he (degree v he) d atNone (uf _ (notMem hv))).1
      else same_row G E he d (uf _ (notMem hv))
  · exact fun v he hv => (biased_row G E he (degree v he) d atNone (uf _ (notMem hv))).2

/-- The guard and a second private neighbour form a triangle with the site.
Only the guard's degree is restricted. -/
def Guarded (G : SimpleGraph V) (H Y : Set V) (y : V) : Prop :=
  ∃ u w, u ∉ H ∪ Y ∧ w ∉ H ∧ G.Adj y u ∧ G.Adj y w ∧ G.Adj u w ∧
    ((G.neighborSet u).encard = 3 ∨ (G.neighborSet u).encard = 4)

private theorem site_opponent (G : SimpleGraph V) (H Y : Set V) (c : V → Bool)
    {y : V} (cy : c y = true) (guarded : Guarded G H Y y)
    (free : ∀ v, v ∉ H ∪ Y → UnfriendlyAt G (fun w => some (c w)) v)
    (strict : ∀ v, (G.neighborSet v).encard = 4 → v ∉ H ∪ Y →
      c v = true → 3 ≤ (Energy.oppositeSet G c v).encard) :
    ∃ w ∉ H, G.Adj y w ∧ c w = false := by
  classical
  obtain ⟨u, w, hu, hw, hyu, hyw, huw, degree⟩ := guarded
  by_cases cu : c u = true
  · refine ⟨w, hw, hyw, ?_⟩
    apply Bool.eq_false_iff.mpr
    intro cw
    let O := Energy.oppositeSet G c u
    let N := G.neighborSet u
    have inN : O ⊆ N := fun _ hx => hx.1
    have hfin : N.Finite :=
      Set.encard_ne_top_iff.mp (degree.elim (fun e => e ▸ by decide) (fun e => e ▸ by decide))
    have ofi := hfin.subset inN
    have sum := Set.ncard_sdiff_add_ncard_of_subset inN hfin
    have ys : y ∈ N \ O := ⟨hyu.symm, fun h => h.2 (cy.trans cu.symm)⟩
    have ws : w ∈ N \ O := ⟨huw, fun h => h.2 (cw.trans cu.symm)⟩
    have bound := Set.ncard_le_ncard (Set.pair_subset ys ws) hfin.sdiff
    rw [Set.ncard_pair hyw.ne] at bound
    rcases degree with three | four
    · have opp := quota_of_unfriendly G c u 2 (by rw [three]; decide) (free u hu)
      have card : N.ncard = 3 := (Nat.cast_inj (R := ℕ∞)).mp (hfin.cast_ncard_eq.trans three)
      have enough : 2 ≤ O.ncard := ENat.natCast_le_natCast.mp (ofi.cast_ncard_eq.symm ▸ opp)
      omega
    · have card : N.ncard = 4 := (Nat.cast_inj (R := ℕ∞)).mp (hfin.cast_ncard_eq.trans four)
      have enough : 3 ≤ O.ncard :=
        ENat.natCast_le_natCast.mp (ofi.cast_ncard_eq.symm ▸ strict u four hu cu)
      omega
  · exact ⟨u, fun h => hu (Or.inl h), hyu, Bool.eq_false_iff.mpr cu⟩

private theorem site_unfriendly (G : SimpleGraph V) (H : Set V) (c : V → Bool)
    {y : V} (cy : c y = true) (zero : ∀ h ∈ H, c h = false)
    (small : (G.neighborSet y).encard ≤ 6) (anchors : 2 ≤ (G.neighborSet y ∩ H).encard)
    (privateOpp : ∃ w ∉ H, G.Adj y w ∧ c w = false) :
    UnfriendlyAt G (fun w => some (c w)) y := by
  classical
  obtain ⟨w, hw, hyw, cw⟩ := privateOpp
  let A := G.neighborSet y ∩ H
  have hfin := Set.encard_ne_top_iff.mp (lt_of_le_of_lt small (by decide)).ne
  have sub : insert w A ⊆ Energy.oppositeSet G c y := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | ha
    · exact ⟨hyw, by simp [cw, cy]⟩
    · exact ⟨ha.1, by simp [zero z ha.2, cy]⟩
  have hnew : w ∉ A := fun h => hw h.2
  have enough := Set.encard_le_encard sub
  rw [Set.encard_insert_of_notMem hnew] at enough
  apply TrianglePorts.unfriendly_of_opponent_quota G c y 3 hfin
  · exact ENat.natCast_le_natCast.mp (hfin.cast_ncard_eq.le.trans small)
  · exact (add_le_add_left anchors 1).trans enough

/-- Infinitely many guarded sites at each precoloured hub suffice for every ordinal clock. -/
theorem all_clocks [Countable V] (G : SimpleGraph V) (H Y : Set V) (disj : Disjoint H Y)
    (few : {v | v ∉ H ∪ Y ∧ (G.neighborSet v).Infinite}.Finite)
    (witnesses : ∀ h ∈ H, (G.neighborSet h ∩ Y).Infinite)
    (small : ∀ y ∈ Y, (G.neighborSet y).encard ≤ 6)
    (anchors : ∀ y ∈ Y, 2 ≤ (G.neighborSet y ∩ H).encard)
    (guards : ∀ y ∈ Y, Guarded G H Y y) :
    ∀ α : Ordinal, PartitionerWins G (emptyPartition V) α := by
  classical
  let p (v : V) := decide (v ∉ H)
  obtain ⟨c, fixed, free, strict⟩ :=
    biased_extension G (H ∪ Y) {v | (G.neighborSet v).encard = 4} p (fun _ h => h) few
  have zero (h : V) (hh : h ∈ H) : c h = false := (fixed (Or.inl hh)).trans (by simp [p, hh])
  have one (y : V) (hy : y ∈ Y) : c y = true :=
    (fixed (Or.inr hy)).trans (by simp [p, Set.disjoint_right.mp disj hy])
  apply all_clocks_of_global G
  refine ⟨fun w => some (c w), fun v => ?_⟩
  by_cases hh : v ∈ H
  · apply Energy.unfriendly_of_infinite_opposite
    exact (witnesses v hh).mono fun w hw => ⟨hw.1, by simp [one w hw.2, zero v hh]⟩
  · by_cases hy : v ∈ Y
    · exact site_unfriendly G H c (one v hy) zero (small v hy) (anchors v hy)
        (site_opponent G H Y c (one v hy) (guards v hy) free strict)
    · exact free v (fun h => h.elim hh hy)

end TenChallenges.Continuation.GuardedSites

theorem solution {V : Type u} [Countable V] (G : SimpleGraph V) (H Y : Set V) (disj : Disjoint H Y)
    (few : {v | v ∉ H ∪ Y ∧ (G.neighborSet v).Infinite}.Finite)
    (witnesses : ∀ h ∈ H, (G.neighborSet h ∩ Y).Infinite)
    (small : ∀ y ∈ Y, (G.neighborSet y).encard ≤ 6)
    (anchors : ∀ y ∈ Y, 2 ≤ (G.neighborSet y ∩ H).encard)
    (guards : ∀ y ∈ Y, ∃ u w, u ∉ H ∪ Y ∧ w ∉ H ∧ G.Adj y u ∧ G.Adj y w ∧ G.Adj u w ∧
      ((G.neighborSet u).encard = 3 ∨ (G.neighborSet u).encard = 4))
    (r : Ordinal.{v}) : PartitionerWins G (emptyPartition V) r :=
  TenChallenges.Continuation.GuardedSites.all_clocks G H Y disj few witnesses small anchors guards r

#print axioms solution
