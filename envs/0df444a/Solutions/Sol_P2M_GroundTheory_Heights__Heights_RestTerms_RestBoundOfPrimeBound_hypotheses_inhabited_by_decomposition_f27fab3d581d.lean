-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundOfPrimeBound_hypotheses_inhabited_by_decomposition_f27fab3d581d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:14.529745+00:00
-- url     : https://prove2.me/submissions/175397d5-a55f-4e4e-8196-ec6e41998b36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_restTerm_b831e71f17f7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ChebyshevThetaBound_intersectionNumber_baseChange_1e58a3fff588
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ExponentialTail_intersectionNumber_baseChange_69f6990adeee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_GeometricTail_intersectionNumber_baseChange_cf5b94796824
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestConstants_intersectionNumber_baseChange_3cbe9c9bc2bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankBound_intersectionNumber_baseChange_63d64eced049
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankWeakHypothesis_intersectionNumber_baseChange_46cb8718a615
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_XBound_intersectionNumber_baseChange_3674cb61fc35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_XOverPrime_intersectionNumber_baseChange_8ed2297f9f86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_J_eq_083d9017b1ba


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace RestBoundOfPrimeBound
theorem _root_.solution
    (s : ℕ → ℕ → Fin 1 → Fin 1) (e : ℕ → ℕ → Fin 1 → ℕ → ℚ)
    (he : ∀ p n τ k, e p n τ k = 1 ∨ e p n τ k = -1) :
    4 * ((1 : ℕ) : ℝ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 ∧
    ∀ p : ℕ, p.Prime → (16 : ℝ) < p →
      |restPrimeModel 1 1 1 .last inhQ s e p| ≤
        1.5 * ((1 : ℕ) : ℝ) * (restX 1 1 : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((1 * (1 * 1) + 1 : ℕ) : ℝ) * |(fibreDegree 1 1 1 .last : ℝ)| := by
  refine ⟨by norm_num, ?_⟩
  intro p hp _
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hI : Finset.Icc 2 (1 + 1) = ({2} : Finset ℕ) := by decide
  have hterm : ∀ n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ *
      ((e p (n + 1) 0 2 * restTerm 1 (1 + 1) inhQ 2 0
        (smallPowerSum 1 1 1 .last (2 - 1) (s p (n + 1) 0)) : ℚ) : ℝ) =
      ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ)) := by
    intro n
    rw [inh_restTerm]
    push_cast
    ring
  have hnorm : ∀ n : ℕ, ‖((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))‖ =
      ((p : ℝ) ^ ((n + 1) * 2))⁻¹ := by
    intro n
    have h1 : |(e p (n + 1) 0 2 : ℝ)| = 1 := by
      rcases he p (n + 1) 0 2 with h | h <;> simp [h]
    have hpos : (0 : ℝ) < ((p : ℝ) ^ ((n + 1) * 2))⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_neg, h1, mul_one, abs_of_pos hpos]
  obtain ⟨hs, hle⟩ := GeometricTail.intersectionNumber_baseChange (p : ℝ) 2 hp2 (by norm_num)
  have hs' : Summable
      (fun n : ℕ => ‖((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))‖) := by
    simp_rw [hnorm]
    exact hs
  have hS : |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))| ≤
      2 * ((p : ℝ) ^ 2)⁻¹ := by
    calc |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))|
        = ‖∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑' n : ℕ, ‖((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))‖ :=
          norm_tsum_le_tsum_norm hs'
      _ = ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ := by simp_rw [hnorm]
      _ ≤ 2 * ((p : ℝ) ^ 2)⁻¹ := hle
  have hmodel : restPrimeModel 1 1 1 .last inhQ s e p =
      Real.log p * ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ)) := by
    rw [restPrimeModel, hI, Fin.sum_univ_one, Finset.sum_singleton]
    simp_rw [hterm]
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hX : (restX 1 1 : ℝ) = 6 := by norm_num [restX]
  have ht : 0 ≤ Real.log p * ((p : ℝ) ^ 2)⁻¹ := by positivity
  rw [hmodel, abs_mul, abs_of_nonneg hlog, hX, inh_J_eq]
  calc Real.log p * |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * 2))⁻¹ * (-(e p (n + 1) 0 2 : ℝ))|
      ≤ Real.log p * (2 * ((p : ℝ) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hS hlog
    _ = 2 * (Real.log p * ((p : ℝ) ^ 2)⁻¹) := by ring
    _ ≤ 18 * (Real.log p * ((p : ℝ) ^ 2)⁻¹) := by linarith
    _ = 1.5 * ((1 : ℕ) : ℝ) * 6 * (Real.log p / (p : ℝ) ^ 2) *
          ((1 * (1 * 1) + 1 : ℕ) : ℝ) * |((-1 : ℚ) : ℝ)| := by
      rw [div_eq_mul_inv]
      norm_num
      ring
end RestBoundOfPrimeBound
end GroundTheory.Heights₂.Heights.RestTerms
