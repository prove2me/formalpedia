-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestPrimeBoundOfFactor_proof_99faba5c2a4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:14.993435+00:00
-- url     : https://prove2.me/submissions/f582344c-e13d-49f4-a1c0-1716a1aa4492

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPrimeBoundOfFactor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ChebyshevThetaBound_intersectionNumber_baseChange_1e58a3fff588
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ExponentialTail_intersectionNumber_baseChange_69f6990adeee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_GeometricTail_intersectionNumber_baseChange_cf5b94796824
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestConstants_intersectionNumber_baseChange_3cbe9c9bc2bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankBound_intersectionNumber_baseChange_63d64eced049
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankWeakHypothesis_intersectionNumber_baseChange_46cb8718a615
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_XBound_intersectionNumber_baseChange_3674cb61fc35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_XOverPrime_intersectionNumber_baseChange_8ed2297f9f86


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
open Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace RestPrimeBoundOfFactor
theorem _root_.solution (h₁ : RestInnerTsumBound.Statement)
    (h₂ : RestKSumBound.Statement) : RestPrimeBoundOfFactor.Statement := by
  intro f r a c B₀ hf hr ha hB Q hT s e he p hp hpB
  set Y : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hY
  set X : ℝ := (restX r a : ℝ) with hX
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hX0 : 0 ≤ X := by rw [hX]; unfold restX; positivity
  have hN : 2 ≤ r + a := by omega
  have hXp : X ≤ 3 / 8 * (p : ℝ) := by
    have := XOverPrime.intersectionNumber_baseChange f r a B₀ p hf hN hB hpB
    rw [div_le_iff₀ hp0] at this
    linarith
  have hY0 : 0 ≤ Y := by positivity

  have hterm : ∀ τ : Fin f, ∀ k ∈ Finset.Icc 2 (r + a),
      |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
        ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
          (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)| ≤
        (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹) := by
    intro τ k hk
    rw [Finset.mem_Icc] at hk
    refine (h₁ (p : ℝ) k _ _ hp2 (by omega) ?_).2
    intro n
    have hb := hT k hk.1 hk.2 τ (s p (n + 1) τ)
    have habs : |e p (n + 1) τ k * restTerm f (r + a) Q k τ
        (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| =
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| := by
      rw [abs_mul]
      rcases he p (n + 1) τ k with h | h <;> simp [h]
    rw [← Rat.cast_abs, habs]
    calc ((|restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| : ℚ) : ℝ)
        ≤ ((((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ) : ℚ) : ℝ) := Rat.cast_le.mpr hb
      _ = Y * X ^ (k - 1) / (k.factorial : ℝ) := by
        rw [hY, hX]; push_cast; ring
  have hsumk := h₂ (p : ℝ) X (r + a) hp0 hX0 hXp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  unfold restPrimeModel
  rw [abs_mul, abs_of_nonneg hlog]
  calc Real.log p * |∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a), ∑' n : ℕ,
        ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
          ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
            (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)|
      ≤ Real.log p * ∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a),
          (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hlog
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact hterm τ k hk
    _ = Real.log p * ((f : ℝ) * (Y * ∑ k ∈ Finset.Icc 2 (r + a),
          2 * ((p : ℝ) ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ Real.log p * ((f : ℝ) * (Y * (1.5 * X / (p : ℝ) ^ 2))) := by
        gcongr
    _ = 1.5 * (f : ℝ) * X * (Real.log p / (p : ℝ) ^ 2) * Y := by ring
    _ = 1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by
        rw [hY, hX]; ring
end RestPrimeBoundOfFactor
end GroundTheory.Heights₂.Heights.RestTerms
