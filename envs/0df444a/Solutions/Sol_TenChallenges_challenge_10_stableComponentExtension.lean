-- Prove2me | solution 1 for TenChallenges.challenge_10_stableComponentExtension
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T21:02:14.621343+00:00
-- url     : https://prove2.me/submissions/5c3fe7a1-001a-455e-9627-b96600816204

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

/- Inlined from Continuation/UnfriendlyThreeBoundaryGraph.lean. -/
namespace TenChallenges.Continuation.ThreeBoundaryGraph

variable {V : Type u}

abbrev finiteGraph (G : SimpleGraph V) := G.induce {x | (G.neighborSet x).Finite}

abbrev Component (G : SimpleGraph V) := (finiteGraph G).ConnectedComponent

end TenChallenges.Continuation.ThreeBoundaryGraph

/- Inlined from Continuation/UnfriendlyStableComponents.lean. -/
/-!
# Stable colourings of the finite-degree components

Fix the colours of the infinite-degree vertices. Each component of the induced
graph on the other vertices can choose its own locally stable colouring. A
component can supply a hub if one such choice gives the hub an opponent.

In a countable graph, assign distinct components to the requests indexed by
(hub, natural number). Paste their colourings along the fixed hubs and use a
stable default colouring on the remaining components. If every component is
finite, any extension must satisfy the same support condition.
-/

set_option autoImplicit false


namespace TenChallenges.Continuation.StableComponents

open ThreeBoundaryGraph Energy

variable {V : Type u} (G : SimpleGraph V)

/-- Vertices of infinite degree, whose colours are prescribed. -/
def hubs : Set V := {x | (G.neighborSet x).Infinite}

/-- The colouring agrees with the prescribed hub colours and is unfriendly at
every vertex of the component. The neighbours of an interior vertex lie in
the component or on its hub boundary. -/
def Stable (q : V → Bool) (C : Component G) (c : V → Bool) : Prop :=
  Set.EqOn c q (hubs G) ∧ ∀ y ∈ C.supp, UnfriendlyAt G (fun w => some (c w)) y.val

/-- An interior neighbour of the hub has the opposite colour. -/
def Supplies (q : V → Bool) (x : V) (C : Component G) (c : V → Bool) : Prop :=
  ∃ y ∈ C.supp, G.Adj x y.val ∧ c y.val ≠ q x

private theorem necessary (q c : V → Bool) (hfix : Set.EqOn c q (hubs G))
    (hc : ∀ x, UnfriendlyAt G (fun w => some (c w)) x)
    (hfinite : ∀ C : Component G, C.supp.Finite) (x : V) (hx : x ∈ hubs G) :
    (oppositeSet G q x ∩ hubs G).Infinite ∨
      {C | ∃ d, Stable G q C d ∧ Supplies G q x C d}.Infinite := by
  refine or_iff_not_imp_left.mpr fun hdir hcomp => ?_
  let candidates := {C | ∃ d, Stable G q C d ∧ Supplies G q x C d}
  have hu : (⋃ C ∈ candidates, Subtype.val '' C.supp).Finite :=
    hcomp.biUnion fun C _ => (hfinite C).image Subtype.val
  apply infinite_opposite_of_unfriendly G c x hx (hc x)
    (((Set.not_infinite.mp hdir).union hu).subset ?_)
  intro w hw
  by_cases hfin : (G.neighborSet w).Finite
  · let y : {z | (G.neighborSet z).Finite} := ⟨w, hfin⟩
    let C := (finiteGraph G).connectedComponentMk y
    have hy : y ∈ C.supp := rfl
    have hC : C ∈ candidates := ⟨c, ⟨hfix, fun z _ => hc z.val⟩, y, hy, hw.1,
      fun e => hw.2 (e.trans (hfix hx).symm)⟩
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨C, hC, y, hy, rfl⟩)
  · exact Or.inl ⟨⟨hw.1, fun e => hw.2 ((hfix hfin).trans (e.trans (hfix hx).symm))⟩, hfin⟩

open Classical in
private noncomputable def glue (q : V → Bool) (d : Component G → V → Bool) (x : V) : Bool :=
  if hx : (G.neighborSet x).Finite then
    d ((finiteGraph G).connectedComponentMk ⟨x, hx⟩) x else q x

private theorem glue_hubs (q : V → Bool) (d : Component G → V → Bool) :
    Set.EqOn (glue G q d) q (hubs G) :=
  fun _ hx => dif_neg hx

private theorem glue_component (q : V → Bool) (d : Component G → V → Bool)
    (C : Component G) (y : {w | (G.neighborSet w).Finite}) (hy : y ∈ C.supp) :
    glue G q d y.val = d C y.val :=
  (dif_pos y.property).trans (congrArg (fun D => d D y.val) ((C.mem_supp_iff y).mp hy))

private theorem unfriendly_congr {c d : V → Bool} (x : V) (hx : c x = d x)
    (hn : ∀ y ∈ G.neighborSet x, c y = d y)
    (hu : UnfriendlyAt G (fun w => some (c w)) x) :
    UnfriendlyAt G (fun w => some (d w)) x := by
  have htype (b : Bool) : NeighColored G (fun w => some (c w)) x (some b) =
      NeighColored G (fun w => some (d w)) x (some b) :=
    congrArg (fun S : Set V => ↥S) (Set.ext fun y => and_congr_right fun hy =>
      Iff.of_eq (congrArg (fun z : Bool => some z ∈ ({some b} : Set (Option Bool))) (hn y hy)))
  simpa only [UnfriendlyAt, hx, htype] using hu

private theorem glue_stable (q : V → Bool) (d : Component G → V → Bool)
    (hd : ∀ C, Stable G q C (d C)) (x : V) (hx : (G.neighborSet x).Finite) :
    UnfriendlyAt G (fun w => some (glue G q d w)) x :=
  let y : {w | (G.neighborSet w).Finite} := ⟨x, hx⟩
  let C := (finiteGraph G).connectedComponentMk y
  have hy : y ∈ C.supp := rfl
  unfriendly_congr G x (glue_component G q d C y hy).symm
    (fun w hw => (Classical.em ((G.neighborSet w).Finite)).elim
      (fun hfin => (glue_component G q d C ⟨w, hfin⟩ (C.mem_supp_of_adj_mem_supp hy
        (show (finiteGraph G).Adj y ⟨w, hfin⟩ from hw))).symm)
      (fun hinf => ((hd C).1 hinf).trans (glue_hubs G q d hinf).symm))
    ((hd C).2 y hy)

private theorem glue_opponents (q : V → Bool) (d : Component G → V → Bool)
    (x : V) (hx : x ∈ hubs G) (hs : {C | Supplies G q x C (d C)}.Infinite) :
    (oppositeSet G (glue G q d) x).Infinite := by
  let A := {C | Supplies G q x C (d C)}
  haveI : Infinite A := Set.infinite_coe_iff.mpr hs
  choose y hy hadj hne using fun C : A => C.property
  refine Set.infinite_of_injective_forall_mem (f := fun C : A => (y C).val) ?_
    (fun C => ⟨hadj C, fun e => hne C
      (((glue_component G q d C.val (y C) (hy C)).symm.trans e).trans (glue_hubs G q d hx))⟩)
  exact fun {C D} e => Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (hy C) ((congrArg (fun w => w ∈ D.val.supp) (Subtype.ext e : y C = y D)).mpr (hy D)))

open Classical in
private theorem distinct_nat {κ : Type*} (s : ℕ → Set κ) (hs : ∀ n, (s n).Infinite) :
    ∃ f : ℕ → κ, Function.Injective f ∧ ∀ n, f n ∈ s n :=
  let pick (n : ℕ) (D : Finset κ) := Classical.choose ((hs n).exists_notMem_finset D)
  have hp (n : ℕ) (D : Finset κ) : pick n D ∈ s n ∧ pick n D ∉ D :=
    Classical.choose_spec ((hs n).exists_notMem_finset D)
  let used : ℕ → Finset κ := Nat.rec ∅ fun n D => insert (pick n D) D
  let f (n : ℕ) := pick n (used n)
  have step (n : ℕ) : f n ∈ used (n + 1) := Finset.mem_insert_self _ _
  have mono : Monotone used := monotone_nat_of_le_succ fun _ => Finset.subset_insert _ _
  have fresh {i j : ℕ} (hij : i < j) : f i ≠ f j := fun e =>
    (hp j (used j)).2 ((congrArg (fun z => z ∈ used j) e).mp (mono hij (step i)))
  ⟨f, Function.injective_iff_pairwise_ne.mpr (fun _ _ h =>
    (lt_or_gt_of_ne h).elim (fun hlt => fresh hlt) (fun hgt => (fresh hgt).symm)),
    fun n => (hp n (used n)).1⟩

private theorem distinct_choices {ι κ : Type*} [Countable ι] (s : ι → Set κ)
    (hs : ∀ i, (s i).Infinite) :
    ∃ f : ι → κ, Function.Injective f ∧ ∀ i, f i ∈ s i := by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨isEmptyElim, fun {i} => isEmptyElim i, fun i => isEmptyElim i⟩
  | inr hnonempty =>
    obtain ⟨e, he⟩ := exists_surjective_nat ι
    obtain ⟨f, hf, hfmem⟩ := distinct_nat (fun n => s (e n)) (fun n => hs (e n))
    exact ⟨f ∘ Function.surjInv he, hf.comp (Function.injective_surjInv he),
      fun i => by
        simpa only [Function.surjInv_eq, Function.comp_apply] using hfmem (Function.surjInv he i)⟩

private theorem choose_stable [Countable V] (q : V → Bool) (J : Set V)
    (h : ∀ x ∈ J, {C | ∃ c, Stable G q C c ∧ Supplies G q x C c}.Infinite) :
    ∃ d : Component G → V → Bool, (∀ C, Stable G q C (d C)) ∧
      ∀ x ∈ J, {C | Supplies G q x C (d C)}.Infinite := by
  obtain ⟨f, hf, hmem⟩ := distinct_choices
    (fun i : J × ℕ => {C | ∃ c, Stable G q C c ∧ Supplies G q i.1.val C c})
    (fun i => h i.1.val i.1.property)
  obtain ⟨base, hfix, hmax⟩ := StrongMaximalCompactness.exists_strongMaximal_eqOn G (hubs G) q
  choose col hstable hsupply using hmem
  let d := Function.extend f col (fun _ => base)
  refine ⟨d, ?_, fun x hx => Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => f (⟨x, hx⟩, n)) (fun _ _ e => congrArg Prod.snd (hf e))
    (fun n => by simpa only [Set.mem_ofPred_eq, d, hf.extend_apply] using hsupply (⟨x, hx⟩, n))⟩
  intro C
  by_cases hC : ∃ i, f i = C
  · obtain ⟨i, rfl⟩ := hC
    simpa only [d, hf.extend_apply] using hstable i
  · rw [show d C = base from Function.extend_apply' col (fun _ => base) C hC]
    exact ⟨hfix, fun y _ => unfriendlyAt_of_strongMaximal G _ base hmax y.val
      (fun hy => hy y.property) y.property⟩

/-- A prescribed hub assignment extends whenever each hub already has infinitely
many hub opponents or infinitely many components that can individually supply it.
The components themselves may be infinite. -/
theorem exists_extension_of_support [Countable V] (q : V → Bool)
    (hs : ∀ x ∈ hubs G, (oppositeSet G q x ∩ hubs G).Infinite ∨
      {C | ∃ d, Stable G q C d ∧ Supplies G q x C d}.Infinite) :
    ∃ c : V → Bool, Set.EqOn c q (hubs G) ∧
      ∀ x, UnfriendlyAt G (fun w => some (c w)) x := by
  let J := {x | x ∈ hubs G ∧ ¬ (oppositeSet G q x ∩ hubs G).Infinite}
  obtain ⟨d, hd, hsupport⟩ := choose_stable G q J
    (fun x hx => (hs x hx.1).resolve_left hx.2)
  have hfix := glue_hubs G q d
  refine ⟨glue G q d, hfix, fun x => ?_⟩
  by_cases hx : (G.neighborSet x).Finite
  · exact glue_stable G q d hd x hx
  · apply unfriendly_of_infinite_opposite
    by_cases hdir : (oppositeSet G q x ∩ hubs G).Infinite
    · exact hdir.mono fun w hw => ⟨hw.1.1, fun e =>
        hw.1.2 ((hfix hw.2).symm.trans (e.trans (hfix hx)))⟩
    · exact glue_opponents G q d x hx (hsupport x ⟨hx, hdir⟩)

/-- For finite components of the finite-degree graph, individual component
support and direct hub opponents characterize extendibility of the hub colours. -/
theorem extension_iff [Countable V] (q : V → Bool)
    (hfinite : ∀ C : Component G, C.supp.Finite) :
    (∃ c : V → Bool, Set.EqOn c q (hubs G) ∧
      ∀ x, UnfriendlyAt G (fun w => some (c w)) x) ↔
    ∀ x ∈ hubs G, (oppositeSet G q x ∩ hubs G).Infinite ∨
      {C | ∃ d, Stable G q C d ∧ Supplies G q x C d}.Infinite :=
  ⟨fun ⟨c, hfix, hc⟩ => necessary G q c hfix hc hfinite, exists_extension_of_support G q⟩

end TenChallenges.Continuation.StableComponents

theorem solution {V : Type u} [Countable V] (G : SimpleGraph V)
    (q : V → Bool) (hfinite : ∀ C : (G.induce {v : V | (G.neighborSet v).Finite}).ConnectedComponent, C.supp.Finite) :
    let I : Set V := {v | (G.neighborSet v).Infinite}
    (∃ c : V → Bool, Set.EqOn c q I ∧ ∀ v, UnfriendlyAt G (fun w => some (c w)) v) ↔
      ∀ x ∈ I, ({y : V | G.Adj x y ∧ q y ≠ q x} ∩ I).Infinite ∨
        {C : (G.induce {v : V | (G.neighborSet v).Finite}).ConnectedComponent |
          ∃ d : V → Bool,
            (Set.EqOn d q I ∧ ∀ y ∈ C.supp, UnfriendlyAt G (fun w => some (d w)) y.val) ∧
            ∃ y ∈ C.supp, G.Adj x y.val ∧ d y.val ≠ q x}.Infinite :=
  TenChallenges.Continuation.StableComponents.extension_iff G q hfinite

#print axioms solution
