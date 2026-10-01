-- Prove2me | solution 1 for RobustMDP.FiniteHorizon.worstCase_policy_recursion
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:44:39.164532+00:00
-- url     : https://prove2.me/submissions/fb567cb5-833d-4ccb-a6eb-35f34c8ccfa4

import Theorems.Thm_RobustMDP_FiniteHorizon_robust_dynamic_programming
import Mathlib.Tactic
open RobustMDP.FiniteHorizon
namespace CRobust

theorem state_simplex {n N : ℕ} {A : Type} (π : ControlPolicy n N A)
    (P : Fin N → A → Fin n → Fin n → ℝ) (i₀ : Fin n)
    (hP : ∀ t a i, P t a i ∈ stdSimplex ℝ (Fin n)) :
    ∀ t ≤ N, stateDist π P i₀ t ∈ stdSimplex ℝ (Fin n) := by
  intro t
  induction t with
  | zero =>
    intro _
    simpa [stateDist,eq_comm] using ite_eq_mem_stdSimplex ℝ i₀
  | succ t ih =>
    intro ht
    have htn : t<N := by omega
    have hprev := ih (by omega)
    constructor
    · intro j
      simp only [stateDist,htn,dite_true]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hprev.1 i) ((hP ⟨t,htn⟩ (π ⟨t,htn⟩ i) i).1 j))
    · simp only [stateDist,htn,dite_true]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, (hP _ _ _).2,mul_one]
      exact hprev.2

theorem cost_upper {n N : ℕ} {A : Type} (M : Model n N A) (i₀ : Fin n)
    (π : ControlPolicy n N A) (P : Fin N → A → Fin n → Fin n → ℝ)
    (hP : ∀ t a i, P t a i ∈ stdSimplex ℝ (Fin n)) :
    M.expectedCost i₀ π P ≤ (∑ t : Fin N, ∑ i, |M.cost t i (π t i)|)+∑ i, |M.terminalCost i| := by
  have hterm : ∀ t ≤ N, ∀ i (a : ℝ), stateDist π P i₀ t i*a ≤ |a| := by
    intro t ht i a
    have hp := mem_Icc_of_mem_stdSimplex (state_simplex π P i₀ hP t ht) i
    exact (mul_le_mul_of_nonneg_left (le_abs_self a) hp.1).trans (by nlinarith [hp.2,abs_nonneg a])
  unfold Model.expectedCost
  apply add_le_add
  · exact Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun i _ => hterm t (Nat.le_of_lt t.isLt) i _))
  · exact Finset.sum_le_sum (fun i _ => hterm N le_rfl i _)

theorem nature_nonempty {n N : ℕ} {A : Type} (M : Model n N A) : Nonempty M.NaturePolicy := by
  classical
  exact ⟨⟨fun _ a i => (M.rows_nonempty a i).choose,fun _ a i => (M.rows_nonempty a i).choose_spec⟩⟩
end CRobust

namespace CRobust

theorem cost_congr {n N : ℕ} {A B : Type} (M : Model n N A) (M' : Model n N B) (i₀ : Fin n)
    (π : ControlPolicy n N A) (π' : ControlPolicy n N B)
    (P : Fin N → A → Fin n → Fin n → ℝ) (P' : Fin N → B → Fin n → Fin n → ℝ)
    (hc : ∀ t i, M.cost t i (π t i)=M'.cost t i (π' t i))
    (ht : M.terminalCost=M'.terminalCost)
    (hp : ∀ t i, P t (π t i) i=P' t (π' t i) i) :
    M.expectedCost i₀ π P=M'.expectedCost i₀ π' P' := by
  have hstate : ∀ k, stateDist π P i₀ k=stateDist π' P' i₀ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      funext j
      simp only [stateDist,ih]
      split_ifs with h
      · exact Finset.sum_congr rfl (fun i _ => by rw [hp])
      · rfl
  simp only [Model.expectedCost,hstate,hc,ht]
end CRobust

theorem solution {n N : ℕ} {A : Type} (M : Model n N A) (i₀ : Fin n)
    (π : ControlPolicy n N A) :
    IsLUB (Set.range fun τ : M.NaturePolicy => M.expectedCost i₀ π τ.1)
      (M.policyValue π 0 i₀) := by
  classical
  haveI : Nonempty M.NaturePolicy := CRobust.nature_nonempty M
  by_cases hN : N=0
  · subst N
    simpa [Model.expectedCost,Model.policyValue,stateDist] using
      (isLUB_singleton : IsLUB {M.terminalCost i₀} (M.terminalCost i₀))
  haveI : Nonempty (Fin N) := ⟨⟨0,Nat.pos_of_ne_zero hN⟩⟩
  haveI : Nonempty (Fin n) := ⟨i₀⟩
  let M' : Model n N (Fin N×Fin n) := {
    cost := fun t i a => M.cost t i (π a.1 a.2)
    terminalCost := M.terminalCost
    rows := fun a i => M.rows (π a.1 a.2) i
    cost_nonneg := fun t i a => M.cost_nonneg t i (π a.1 a.2)
    rows_subset_simplex := fun a i => M.rows_subset_simplex (π a.1 a.2) i
    rows_nonempty := fun a i => M.rows_nonempty (π a.1 a.2) i }
  let π' : ControlPolicy n N (Fin N×Fin n) := fun t i => (t,i)
  let restrict : M.NaturePolicy → M'.NaturePolicy := fun τ =>
    ⟨fun t a i => τ.1 t (π a.1 a.2) i,fun t a i => τ.2 t (π a.1 a.2) i⟩
  let extend : M'.NaturePolicy → M.NaturePolicy := fun τ =>
    ⟨fun t a i => if a=π t i then τ.1 t (t,i) i else (M.rows_nonempty a i).choose,
      by
        intro t a i
        dsimp only
        split_ifs with h
        · subst a
          exact τ.2 t (t,i) i
        · exact (M.rows_nonempty a i).choose_spec⟩
  have hr : ∀ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1=M'.expectedCost i₀ π' (restrict τ).1 := by
    intro τ
    exact CRobust.cost_congr M M' i₀ π π' τ.1 (restrict τ).1 (fun _ _ => rfl) rfl (fun _ _ => rfl)
  have he : ∀ τ : M'.NaturePolicy, M.expectedCost i₀ π (extend τ).1=M'.expectedCost i₀ π' τ.1 := by
    intro τ
    apply CRobust.cost_congr M M' i₀ π π' (extend τ).1 τ.1 (fun _ _ => rfl) rfl
    intro t i
    simp [extend,π']
  have hrange : (Set.range fun τ : M.NaturePolicy => M.expectedCost i₀ π τ.1)=
      Set.range fun τ : M'.NaturePolicy => M'.expectedCost i₀ π' τ.1 := by
    ext z
    constructor
    · rintro ⟨τ,rfl⟩
      exact ⟨restrict τ,(hr τ).symm⟩
    · rintro ⟨τ,rfl⟩
      exact ⟨extend τ,he τ⟩
  have hv : ∀ t : Fin (N+1), M'.policyValue π' t=M.policyValue π t := by
    intro t
    induction t using Fin.reverseInduction with
    | last => simp [Model.policyValue,M']
    | cast t ih =>
      conv_lhs => rw [Model.policyValue]
      conv_rhs => rw [Model.policyValue]
      simp only [Fin.val_castSucc,t.isLt,dite_true,Fin.eta]
      change (fun i => M.cost t i (π t i)+RobustMDP.Shared.supportFunction (M.rows (π t i) i)
          (M'.policyValue π' (t+1))) =
        (fun i => M.cost t i (π t i)+RobustMDP.Shared.supportFunction (M.rows (π t i) i)
          (M.policyValue π (t+1)))
      rw [show M'.policyValue π' (t+1)=M.policyValue π (t+1) from ih]
  have hval : (⨆ τ : M.NaturePolicy, M.expectedCost i₀ π τ.1)=M.policyValue π 0 i₀ := by
    change sSup (Set.range _) = _
    rw [hrange]
    change (⨆ τ : M'.NaturePolicy, M'.expectedCost i₀ π' τ.1)=_
    rw [(robust_dynamic_programming M' i₀).2.1 π']
    exact congrFun (hv 0) i₀
  have hb : BddAbove (Set.range fun τ : M.NaturePolicy => M.expectedCost i₀ π τ.1) := by
    refine ⟨(∑ t : Fin N, ∑ i, |M.cost t i (π t i)|)+∑ i, |M.terminalCost i|,?_⟩
    rintro z ⟨τ,rfl⟩
    exact CRobust.cost_upper M i₀ π τ.1 (fun t a i => M.rows_subset_simplex a i (τ.2 t a i))
  rw [← hval]
  exact isLUB_csSup (Set.range_nonempty _) hb


