-- Prove2me | solution 1 for RobustMDP.FiniteHorizon.maxmin_recursion
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:43:22.239783+00:00
-- url     : https://prove2.me/submissions/876cda37-e170-4e58-bde1-939b4247428c

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

theorem solution {n N : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n N A) (i₀ : Fin n) :
    IsLUB (Set.range fun τ : M.NaturePolicy => ⨅ π : ControlPolicy n N A, M.expectedCost i₀ π τ.1)
      (M.robustValue 0 i₀) := by
  classical
  haveI : Nonempty M.NaturePolicy := CRobust.nature_nonempty M
  let π₀ : ControlPolicy n N A := fun _ _ => Classical.choice (inferInstance : Nonempty A)
  have hb : BddAbove (Set.range fun τ : M.NaturePolicy => ⨅ π : ControlPolicy n N A, M.expectedCost i₀ π τ.1) := by
    refine ⟨(∑ t : Fin N, ∑ i, |M.cost t i (π₀ t i)|)+∑ i, |M.terminalCost i|,?_⟩
    rintro z ⟨τ,rfl⟩
    exact (ciInf_le (Set.finite_range _).bddBelow π₀).trans
      (CRobust.cost_upper M i₀ π₀ τ.1 (fun t a i => M.rows_subset_simplex a i (τ.2 t a i)))
  rw [← (robust_dynamic_programming M i₀).1.2]
  exact isLUB_csSup (Set.range_nonempty _) hb
