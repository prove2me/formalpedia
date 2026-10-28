-- Prove2me | solution 1 for Q2CandidateTypes.actual_positive_prefix_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:40:04.890002+00:00
-- url     : https://prove2.me/submissions/b0d39522-77e7-43d7-936c-f7b30295b325

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace TournamentHighRows
end TournamentHighRows

section
/-
Semantic high-row bounds for the graded q2/q3 transfer.

The finite high set is connected to actual guard failure sets: every arc to
a high head selects a guard-true child and therefore consumes a failure of
its tail. The tournament edge double count is proved here, not assumed.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace TournamentHighRows
open scoped Classical BigOperators

variable {V X : Type}







theorem mem_arcs (R : V → V → Prop) (S : Finset V) (v w : V) :
    (v,w) ∈ arcs R S ↔ v ∈ S ∧ w ∈ S ∧ R v w := by
  classical
  constructor
  · intro h
    have hf := Finset.mem_filter.mp h
    have hp := Finset.mem_product.mp hf.1
    exact ⟨hp.1, hp.2, hf.2⟩
  · rintro ⟨hv,hw,hR⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv,hw⟩,hR⟩

theorem reverse_arcs_card (R : V → V → Prop) (S : Finset V) :
    (arcs (fun v w => R w v) S).card = (arcs R S).card := by
  classical
  refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
  · intro p hp
    rcases p with ⟨v,w⟩
    rcases (mem_arcs _ S v w).1 hp with ⟨hv,hw,hR⟩
    exact (mem_arcs R S w v).2 ⟨hw,hv,hR⟩
  · intro p hp q hq heq
    exact Prod.swap_injective heq
  · intro p hp
    rcases p with ⟨v,w⟩
    rcases (mem_arcs R S v w).1 hp with ⟨hv,hw,hR⟩
    exact ⟨(w,v), (mem_arcs _ S w v).2 ⟨hw,hv,hR⟩, rfl⟩

theorem arcs_disjoint_reverse (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) : Disjoint (arcs R S) (arcs (fun v w => R w v) S) := by
  classical
  apply Finset.disjoint_left.mpr
  rintro ⟨v,w⟩ hp hq
  have hvw := ((mem_arcs R S v w).1 hp).2.2
  have hwv := ((mem_arcs _ S v w).1 hq).2.2
  have hne : v ≠ w := by
    intro he
    subst w
    exact hR.loopless v hvw
  exact ((hR.orient v w hne).1 hvw) hwv

theorem arcs_union_reverse (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) :
    arcs R S ∪ arcs (fun v w => R w v) S = S.offDiag := by
  classical
  ext p
  rcases p with ⟨v,w⟩
  simp only [Finset.mem_union, mem_arcs, Finset.mem_offDiag]
  constructor
  · rintro (⟨hv,hw,hvw⟩ | ⟨hv,hw,hwv⟩)
    · refine ⟨hv,hw,?_⟩
      intro he
      subst w
      exact hR.loopless v hvw
    · refine ⟨hv,hw,?_⟩
      intro he
      subst w
      exact hR.loopless v hwv
  · rintro ⟨hv,hw,hne⟩
    by_cases hvw : R v w
    · exact Or.inl ⟨hv,hw,hvw⟩
    · exact Or.inr ⟨hv,hw,(hR.orient w v hne.symm).2 hvw⟩

/-- Every unordered pair contributes exactly one directed edge. -/
theorem twice_arcs_card (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) : 2 * (arcs R S).card = S.card * S.card - S.card := by
  classical
  have h := Finset.card_union_of_disjoint (arcs_disjoint_reverse R hR S)
  rw [arcs_union_reverse R hR S, reverse_arcs_card R S, Finset.offDiag_card] at h
  omega

theorem arcs_eq_union_rows (R : V → V → Prop) (S : Finset V) :
    arcs R S = S.biUnion (fun v => ({v} : Finset V).product (outNeighbors R S v)) := by
  classical
  ext p
  rcases p with ⟨v,w⟩
  constructor
  · intro hp
    rcases (mem_arcs R S v w).1 hp with ⟨hv,hw,hR⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hv,Finset.mem_product.mpr ⟨Finset.mem_singleton_self v,?_⟩⟩
    exact Finset.mem_filter.mpr ⟨hw,hR⟩
  · intro hp
    obtain ⟨u,hu,hp⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_product.mp hp with ⟨hvu,hw⟩
    have heq : v = u := Finset.mem_singleton.mp hvu
    subst u
    rcases Finset.mem_filter.mp hw with ⟨hw,hR⟩
    exact (mem_arcs R S v w).2 ⟨hu,hw,hR⟩

theorem arcs_card_le_sum_out (R : V → V → Prop) (S : Finset V) :
    (arcs R S).card ≤ ∑ v ∈ S, (outNeighbors R S v).card := by
  classical
  rw [arcs_eq_union_rows R S]
  calc
    (S.biUnion (fun v => ({v} : Finset V).product (outNeighbors R S v))).card
        ≤ ∑ v ∈ S, (({v} : Finset V).product (outNeighbors R S v)).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ S, (outNeighbors R S v).card := by simp

/-- Necessary budget inequality for every finite tournament and every budget vector. -/
theorem budget_sum_bound (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) (budget : V → ℕ)
    (hbudget : ∀ v ∈ S, (outNeighbors R S v).card ≤ budget v) :
    S.card * (S.card - 1) ≤ 2 * ∑ v ∈ S, budget v := by
  have hsum : (arcs R S).card ≤ ∑ v ∈ S, budget v :=
    (arcs_card_le_sum_out R S).trans (Finset.sum_le_sum hbudget)
  have htwice := Nat.mul_le_mul_left 2 hsum
  rw [twice_arcs_card R hR S] at htwice
  simpa only [Nat.mul_sub_left_distrib, Nat.mul_one] using htwice

theorem card_le_of_outdegree_le (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) (q : ℕ)
    (hbudget : ∀ v ∈ S, (outNeighbors R S v).card ≤ q) : S.card ≤ 2*q+1 := by
  have hb := budget_sum_bound R hR S (fun _ => q) hbudget
  simp only [Finset.sum_const, nsmul_eq_mul] at hb
  by_cases hzero : S.card = 0
  · omega
  · have hpos : 0 < S.card := Nat.pos_of_ne_zero hzero
    have hsub : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hpos
    by_contra hn
    have hlarge : 2*q+2 ≤ S.card := by omega
    have hmul := Nat.mul_le_mul_left S.card hlarge
    nlinarith

section GuardSemantics
variable [Fintype V]



/-- Every edge into a high head consumes an actual failed guard. -/
theorem out_high_subset_failures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (H : Finset V)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c)) (v : V) :
    outNeighbors R H v ⊆ guardFailures R ell P children v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwH,hvw⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hvw, hhigh w hwH (ell v w)⟩

/-- The finite high-row tournament bound, derived from actual selected guards. -/
theorem high_rows_card_le (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (H : Finset V) (q : ℕ)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hbudget : ∀ v ∈ H, (guardFailures R ell P children v).card ≤ q) :
    H.card ≤ 2*q+1 := by
  apply card_le_of_outdegree_le R hR H q
  intro v hv
  exact (Finset.card_le_card (out_high_subset_failures R ell P children H hhigh v)).trans
    (hbudget v hv)







/-- The positive-target prefix through tier b has at most 2b+1 high rows. -/
theorem positive_prefix_card_le (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (pref : Finset V) (b : ℕ)
    (hhigh : ∀ w ∈ pref, ∀ c : Bool, P (children w c))
    (hbudget : ∀ v ∈ pref, (guardFailures R ell P children v).card ≤ b) :
    pref.card ≤ 2*b+1 :=
  high_rows_card_le R hR ell P children pref b hhigh hbudget

end GuardSemantics
end TournamentHighRows








end

section
/-
Exact eight-type decomposition for equal-target graded rows through tolerance 2.

The predicates below refer to the actual child truth values and actual failed
guard count. The classification does not assume a sensitivity bound. It can be
instantiated with target b z := F (threshold b) z, and guard := F g.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Q2CandidateTypes
open scoped Classical
open TournamentHighRows

variable {X V : Type}













theorem positivePrefix_budget_le (q : ℕ) (k : Fin 8)
    (h : ThreeBoundQ2.positivePrefix q k = true) : budget k ≤ q := by
  fin_cases k <;> simp [ThreeBoundQ2.positivePrefix, ThreeBoundQ2.positiveLevel, budget] at h ⊢ <;>
    omega















/-- Every high candidate has both actual guard predicates true. -/
theorem high_guard_true (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z)
    (hh : High guard target Q d x y) : guard x ∧ guard y := by
  rcases hh with ⟨b,hb⟩ | ⟨b,hb⟩
  · exact hb.2
  · exact ⟨hgt b hb.1 x hb.2.2.1,hgt b hb.1 y hb.2.2.2⟩







section ActualRows
variable [Fintype V]











end ActualRows
end Q2CandidateTypes









end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Q2CandidateTypes
end Q2CandidateTypes
open Q2CandidateTypes
open scoped Classical
open TournamentHighRows
variable {X V : Type}
variable [Fintype V]

/-- The exact tag-prefix restrictions used by the executable enumeration follow
    from actual guard budgets. In particular q=0,1,2 gives limits 1,3,5. -/
theorem solution (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (target : ℕ → X → Prop)
    (Q : ℕ) (children : V → Bool → X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z)
    (tag : V → Fin 8)
    (hcount : ∀ v ∈ highRows R ell guard target Q children,
      (guardFailures R ell guard children v).card = budget (tag v)) (q : ℕ) :
    ((highRows R ell guard target Q children).filter
      fun v => ThreeBoundQ2.positivePrefix q (tag v) = true).card ≤ 2*q+1 := by
  classical
  let pref := (highRows R ell guard target Q children).filter
    fun v => ThreeBoundQ2.positivePrefix q (tag v) = true
  apply positive_prefix_card_le R hR ell guard children pref q
  · intro v hv c
    have hvH := (Finset.mem_filter.mp hv).1
    have hh := high_guard_true guard target Q _ _ _ hgt (Finset.mem_filter.mp hvH).2
    cases c
    · exact hh.1
    · exact hh.2
  · intro v hv
    have hvH := (Finset.mem_filter.mp hv).1
    rw [hcount v hvH]
    exact positivePrefix_budget_le q (tag v) (Finset.mem_filter.mp hv).2
end
