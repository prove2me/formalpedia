-- Prove2me | solution 1 for Q2CandidateTypes.actual_high_budget_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:39:56.671011+00:00
-- url     : https://prove2.me/submissions/94d78ec2-856c-406d-8baf-0d6d42619206

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



/-- This proves every subset budget inequality used by the typed-orientation
    generator's necessary sorted-prefix check. -/
theorem every_high_subset_budget_bound (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (H : Finset V) (budget : V → ℕ)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hbudget : ∀ v ∈ H, (guardFailures R ell P children v).card ≤ budget v)
    (S : Finset V) (hSH : S ⊆ H) :
    S.card * (S.card - 1) ≤ 2 * ∑ v ∈ S, budget v := by
  apply budget_sum_bound R hR S budget
  intro v hv
  have hs : ∀ w ∈ S, ∀ c : Bool, P (children w c) :=
    fun w hw c => hhigh w (hSH hw) c
  exact (Finset.card_le_card (out_high_subset_failures R ell P children S hs v)).trans
    (hbudget v (hSH hv))







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

/-- The remaining global degree restriction in allowedTypes is also semantic. -/
theorem solution (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (target : ℕ → X → Prop)
    (Q : ℕ) (children : V → Bool → X)
    (hgt : ∀ b, b ≤ Q → ∀ z, target b z → guard z)
    (tag : V → Fin 8)
    (hcount : ∀ v ∈ highRows R ell guard target Q children,
      (guardFailures R ell guard children v).card = budget (tag v)) :
    let H := highRows R ell guard target Q children
    H.card * (H.card-1) ≤ 2 * ∑ v ∈ H, ThreeBoundQ2.budget (tag v) := by
  classical
  let H := highRows R ell guard target Q children
  have hh : ∀ v ∈ H, ∀ c : Bool, guard (children v c) := by
    intro v hv c
    have hh := high_guard_true guard target Q _ _ _ hgt (Finset.mem_filter.mp hv).2
    cases c
    · exact hh.1
    · exact hh.2
  apply every_high_subset_budget_bound R hR ell guard children H
    (fun v => ThreeBoundQ2.budget (tag v)) hh
  · intro v hv
    exact le_of_eq (hcount v hv)
  · exact Finset.Subset.refl H
end
