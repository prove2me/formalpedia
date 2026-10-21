-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.stage_linear_bound_and_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T12:27:41.782565+00:00
-- url     : https://prove2.me/submissions/5ba2af28-be78-49f6-a92b-284c1a7ae7ad

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage
import Theorems.Thm_ShorNonsmooth_NonlinEq_local_residual_linear_equivalence
import Theorems.Thm_ShorNonsmooth_NonlinEq_stage_orthDir_uniform_lower_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ShorNonsmooth.NonlinEq

theorem solution {n : ℕ} (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i)) (h0 : ∀ i, ψ i 0 = 0) (δ L : ℝ) (hδ : 0 < δ)
    (hLip : ∀ i, ∀ x' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      ∀ x'' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
        ‖gradient (ψ i) x' - gradient (ψ i) x''‖ ≤ L * ‖x' - x''‖)
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ ε₀ > 0, ∃ c₁ > 0, ∃ c₂ > 0, ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsOrthStage ψ x →
      ‖x 0‖ ≤ ε₀ →
      (∀ k, 1 ≤ k → k ≤ n → ‖x k‖ ≤ c₁ * ‖x 0‖) ∧ c₂ * ‖x n‖ ≤ maxResidual ψ (x n) := by
  classical
  obtain ⟨ηa, hηapos, a, hapos, M, hMpos, hlocalData⟩ :=
    local_residual_linear_equivalence ψ hψ h0 hind
  obtain ⟨ηb, hηbpos, b, hbpos, horthData⟩ :=
    stage_orthDir_uniform_lower_bound ψ hψ hind
  let q : ℝ := 1 + M / b
  have hq_one : 1 ≤ q := by
    dsimp [q]
    have hMb : 0 ≤ M / b := div_nonneg hMpos.le hbpos.le
    linarith
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq_one
  let d : ℝ := min ηa ηb
  have hdpos : 0 < d := lt_min hηapos hηbpos
  let ε₀ : ℝ := d / (2 * q ^ n)
  have hqpowpos : 0 < q ^ n := pow_pos hqpos n
  have hε₀pos : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hcritical : q ^ n * ε₀ = d / 2 := by
    dsimp [ε₀]
    field_simp [hqpowpos.ne']
  have hcritical_a : q ^ n * ε₀ < ηa := by
    rw [hcritical]
    exact lt_of_lt_of_le (half_lt_self hdpos) (min_le_left ηa ηb)
  have hcritical_b : q ^ n * ε₀ < ηb := by
    rw [hcritical]
    exact lt_of_lt_of_le (half_lt_self hdpos) (min_le_right ηa ηb)
  refine ⟨ε₀, hε₀pos, q ^ n, hqpowpos, a, hapos, ?_⟩
  intro x hx hx0
  have hstage : ∀ k, k ≤ n → ‖x k‖ ≤ q ^ k * ‖x 0‖ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        cases k with
        | zero => simp
        | succ k =>
            have hkn : k < n := Nat.lt_of_succ_le hk
            have hk_le : k ≤ n := Nat.le_of_lt hkn
            have hprev : ‖x k‖ ≤ q ^ k * ‖x 0‖ :=
              ih k (Nat.lt_succ_self k) hk_le
            have hsmallA : ∀ j ≤ k, ‖x j‖ < ηa := by
              intro j hj
              have hjlt : j < k + 1 := Nat.lt_succ_of_le hj
              have hjle : j ≤ n := le_trans hj hk_le
              have hjb : ‖x j‖ ≤ q ^ j * ‖x 0‖ := ih j hjlt hjle
              have hpow : q ^ j ≤ q ^ n := pow_le_pow_right₀ hq_one hjle
              have hbound : q ^ j * ‖x 0‖ ≤ q ^ n * ε₀ :=
                (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
                  (mul_le_mul_of_nonneg_left hx0 (pow_nonneg hqpos.le n))
              exact lt_of_le_of_lt (le_trans hjb hbound) hcritical_a
            have hsmallB : ∀ j ≤ k, ‖x j‖ < ηb := by
              intro j hj
              have hjlt : j < k + 1 := Nat.lt_succ_of_le hj
              have hjle : j ≤ n := le_trans hj hk_le
              have hjb : ‖x j‖ ≤ q ^ j * ‖x 0‖ := ih j hjlt hjle
              have hpow : q ^ j ≤ q ^ n := pow_le_pow_right₀ hq_one hjle
              have hbound : q ^ j * ‖x 0‖ ≤ q ^ n * ε₀ :=
                (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
                  (mul_le_mul_of_nonneg_left hx0 (pow_nonneg hqpos.le n))
              exact lt_of_le_of_lt (le_trans hjb hbound) hcritical_b
            let kk : Fin n := ⟨k, hkn⟩
            have hψupper : ∀ i, |ψ i (x k)| ≤ M * ‖x k‖ :=
              (hlocalData (x k) (hsmallA k le_rfl)).2
            have horthb : b ≤ ‖orthDir ψ x kk‖ :=
              horthData x kk (by
                intro j
                exact hsmallB j.val (Nat.le_of_lt_succ j.isLt))
            have hdirpos : 0 < ‖orthDir ψ x kk‖ :=
              lt_of_lt_of_le hbpos horthb
            have hstep : ‖x (k + 1)‖ ≤ q * ‖x k‖ := by
              calc
                ‖x (k + 1)‖ =
                    ‖x k - (ψ kk (x k) / ‖orthDir ψ x kk‖ ^ 2) •
                      orthDir ψ x kk‖ := by rw [hx kk]
                _ ≤ ‖x k‖ +
                    ‖(ψ kk (x k) / ‖orthDir ψ x kk‖ ^ 2) •
                      orthDir ψ x kk‖ := norm_sub_le _ _
                _ = ‖x k‖ + |ψ kk (x k)| / ‖orthDir ψ x kk‖ := by
                  rw [norm_smul, Real.norm_eq_abs, abs_div,
                    abs_of_pos (pow_pos hdirpos 2)]
                  field_simp [hdirpos.ne']
                _ ≤ ‖x k‖ + (M * ‖x k‖) / b := by
                  have hnum : |ψ kk (x k)| ≤ M * ‖x k‖ := hψupper kk
                  have hleft : |ψ kk (x k)| / ‖orthDir ψ x kk‖ ≤
                      (M * ‖x k‖) / ‖orthDir ψ x kk‖ :=
                    div_le_div_of_nonneg_right hnum hdirpos.le
                  have hnum_nonneg : 0 ≤ M * ‖x k‖ :=
                    mul_nonneg hMpos.le (norm_nonneg _)
                  have hright : (M * ‖x k‖) / ‖orthDir ψ x kk‖ ≤
                      (M * ‖x k‖) / b :=
                    div_le_div_of_nonneg_left hnum_nonneg hbpos horthb
                  linarith [hleft.trans hright]
                _ = q * ‖x k‖ := by
                  dsimp [q]
                  ring
            calc
              ‖x (k + 1)‖ ≤ q * ‖x k‖ := hstep
              _ ≤ q * (q ^ k * ‖x 0‖) :=
                mul_le_mul_of_nonneg_left hprev hqpos.le
              _ = q ^ (k + 1) * ‖x 0‖ := by
                rw [pow_succ]
                ring
  constructor
  · intro k _ hk
    calc
      ‖x k‖ ≤ q ^ k * ‖x 0‖ := hstage k hk
      _ ≤ q ^ n * ‖x 0‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq_one hk) (norm_nonneg _)
  · have hnA : ‖x n‖ < ηa := by
      have hnbound := hstage n le_rfl
      have hbound : q ^ n * ‖x 0‖ ≤ q ^ n * ε₀ :=
        mul_le_mul_of_nonneg_left hx0 (pow_nonneg hqpos.le n)
      exact lt_of_le_of_lt (le_trans hnbound hbound) hcritical_a
    exact (hlocalData (x n) hnA).1
