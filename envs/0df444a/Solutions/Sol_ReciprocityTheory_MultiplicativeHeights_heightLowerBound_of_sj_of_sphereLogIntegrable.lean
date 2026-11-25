-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.heightLowerBound_of_sj_of_sphereLogIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:42.499118+00:00
-- url     : https://prove2.me/submissions/27adadef-a412-42cf-822f-83f0585bf99d

import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormCoeffSubLeBlockSphereLogMean
import Definitions.Def_ReciprocityTheory_SemistableReduction_HeightLowerBound
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_log_norm_coeff_sub_le_blockSphereLogMean
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_neg_log_norm_coeff_le_finitePlaces
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sum_log_norm_embedding_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hSJ : SJStatement) (hInt : SphereLogIntegrableStatement) :
    HeightLowerBoundStatement := by
  intro K _ _ B n a f hn hf hmh
  classical
  obtain ⟨s, hs⟩ : ∃ s, s ∈ f.support :=
    Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hc : f.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have h1 := neg_log_norm_coeff_le_finitePlaces f s hs
  have h2 : ∀ σ : K →+* ℂ, Real.log ‖σ (f.coeff s)‖ - ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) ≤
      blockSphereMean B n (MvPolynomial.map σ f) := by
    intro σ
    have hmap : IsMultiHomogeneous a (MvPolynomial.map σ f) := by
      intro t ht b
      rw [MvPolynomial.support_map_of_injective _ σ.injective] at ht
      exact hmh t ht b
    exact log_norm_coeff_sub_le_blockSphereLogMean hSJ hInt hn hmap s
      (by rw [MvPolynomial.coeff_map]; exact (map_ne_zero σ).mpr hc)
  have h3 := Finset.sum_le_sum fun (σ : K →+* ℂ) (_ : σ ∈ Finset.univ) ↦ h2 σ
  rw [Finset.sum_sub_distrib, sum_log_norm_embedding_eq _ hc, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card, nsmul_eq_mul] at h3
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold h0
  rw [le_div_iff₀ hd]
  linarith
end ReciprocityTheory.MultiplicativeHeights
