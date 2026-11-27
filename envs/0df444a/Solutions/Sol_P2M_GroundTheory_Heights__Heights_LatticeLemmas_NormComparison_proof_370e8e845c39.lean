-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_NormComparison_proof_370e8e845c39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:25.669213+00:00
-- url     : https://prove2.me/submissions/ad6b5fe3-ad39-4d38-b9ec-f1f85740aa86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PNormComparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_le_of_norm_le_dc01248d9686

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights
open scoped ComplexOrder MatrixOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace NormComparison
theorem _root_.solution : NormComparison.Statement := by
  intro K _ _ M h' A hA
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  have hlog : ∀ σ : K →+* ℂ, Real.log (gramDet h' σ s) ≤
      2 * (Module.finrank (𝓞 K) M.carrier : ℝ) * Real.log (A σ) + Real.log (gramDet M.metric σ s) := by
    intro σ
    have hle := gramDet_le_of_norm_le M.metric h' σ (A σ) (hA σ) hs
    have hg : 0 < gramDet M.metric σ s := gramDet_pos _ σ hs
    have hg' : 0 < gramDet h' σ s := gramDet_pos _ σ hs
    rcases Nat.eq_zero_or_pos (Module.finrank (𝓞 K) M.carrier) with hr | hr
    · have h1 : (max (A σ) 0 ^ 2) ^ Module.finrank (𝓞 K) M.carrier = 1 := by rw [hr, pow_zero]
      have h0 : ((Module.finrank (𝓞 K) M.carrier : ℕ) : ℝ) = 0 := by exact_mod_cast hr
      rw [h1, one_mul] at hle
      rw [h0, mul_zero, zero_mul, zero_add]
      exact Real.log_le_log hg' hle
    · have hpos : 0 < (max (A σ) 0 ^ 2) ^ Module.finrank (𝓞 K) M.carrier :=
        (pos_iff_pos_of_mul_pos (lt_of_lt_of_le hg' hle)).mpr hg
      have hmax : 0 < max (A σ) 0 := by
        rcases (le_max_right (A σ) 0).lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1] at hpos; simp [zero_pow (Nat.pos_iff_ne_zero.mp hr)] at hpos
      have hApos : 0 < A σ := by
        rcases le_or_gt (A σ) 0 with h1 | h1
        · rw [max_eq_right h1] at hmax; exact absurd hmax (lt_irrefl 0)
        · exact h1
      rw [max_eq_left hApos.le] at hle
      calc Real.log (gramDet h' σ s) ≤
            Real.log ((A σ ^ 2) ^ Module.finrank (𝓞 K) M.carrier * gramDet M.metric σ s) :=
            Real.log_le_log hg' hle
        _ = 2 * (Module.finrank (𝓞 K) M.carrier : ℝ) * Real.log (A σ) + Real.log (gramDet M.metric σ s) := by
          rw [Real.log_mul (by positivity) hg.ne', ← pow_mul, Real.log_pow]
          push_cast; ring
  simp only [HermitianBundle.deg, HermitianBundle.arithDegree]
  rw [arithDegree_eq M.metric hs (Fintype.card_fin _), arithDegree_eq h' hs (Fintype.card_fin _)]
  simp only [degreeWith]
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet h' σ s) ≤
      2 * (Module.finrank (𝓞 K) M.carrier : ℝ) * ∑ σ : K →+* ℂ, Real.log (A σ) + ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ s) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun σ _ ↦ hlog σ
  linarith
end NormComparison
end GroundTheory.Heights₂.Heights.LatticeLemmas
