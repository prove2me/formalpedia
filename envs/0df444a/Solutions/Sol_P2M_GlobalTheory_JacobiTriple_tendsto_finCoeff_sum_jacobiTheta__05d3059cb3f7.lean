-- Prove2me | solution 1 for P2M_GlobalTheory_JacobiTriple_tendsto_finCoeff_sum_jacobiTheta__05d3059cb3f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:44:34.122344+00:00
-- url     : https://prove2.me/submissions/4af6f6a9-a167-4ea0-8d8e-ec9b9fdafc40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteCoeffTendstoAndBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleProductLimit
import Theorems.Thm_GlobalTheory_JacobiTriple_norm_exp_pi_I_lt_one
import Theorems.Thm_GlobalTheory_T_jacobiTripleFiniteCoeff_tendsto_and_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
open GlobalTheory GlobalTheory.JacobiTriple
namespace GlobalTheory.JacobiTriple
theorem _root_.solution : ∀ (τ : ℂ) (z : ℂ), 0 < τ.im →
    Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
      GlobalTheory.JacobiTriple.finCoeff (cexp (π * I * τ) ^ 2) n j * jacobiTheta₂_term j z τ)
      Filter.atTop (nhds (jacobiTheta₂ z τ * (GlobalTheory.JacobiTriple.qPochInf (cexp (π * I * τ) ^ 2))⁻¹)) := by
  intro τ z hτ
  set t := cexp (π * I * τ) ^ 2 with ht
  have hs : ‖cexp (π * I * τ)‖ < 1 := norm_exp_pi_I_lt_one τ hτ
  have ht1 : ‖t‖ < 1 := by
    rw [ht, norm_pow]
    nlinarith [norm_nonneg (cexp (π * I * τ))]
  obtain ⟨hlim, C, hC⟩ := GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded t ht1
  have hsum : Summable (fun j : ℤ => C * ‖jacobiTheta₂_term j z τ‖) :=
    ((summable_jacobiTheta₂_term_iff z τ).2 hτ).norm.mul_left C
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun (n : ℕ) (j : ℤ) => finCoeff t n j * jacobiTheta₂_term j z τ)
    (g := fun j => jacobiTheta₂_term j z τ * (qPochInf t)⁻¹) hsum
    (fun j => by
      have := (hlim j).mul_const (jacobiTheta₂_term j z τ)
      simpa [mul_comm] using this)
    (Filter.Eventually.of_forall fun n j => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC n j) (norm_nonneg _))
  rw [tsum_mul_right] at hT
  refine hT.congr (fun n => ?_)
  apply tsum_eq_sum
  intro j hj
  have : ¬ j.natAbs ≤ n := by
    intro h
    apply hj
    rw [Finset.mem_Icc]
    omega
  simp [finCoeff, this]
end GlobalTheory.JacobiTriple
