-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_proof_c35f9e518aa3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:10:03.233906+00:00
-- url     : https://prove2.me/submissions/2ffdfb82-014c-464e-8499-41f3447483ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_isWeightedHomogeneous_aeval_85f3de089ad9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_aeval_8800237edca7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_mkF_chartMonomial_ne_zero_b5c3c1e12aff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_mkF_aeval_forms_d6606fc0914c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_isLive_of_mem_points_f34985632ea7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_joinPt_mem_extPoints_65b19b23e102
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_plusMetric_joinPt_ee8b088ced98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SmallSections
theorem _root_.solution (hForms : ChartFormsAlt.Statement) : SmallSections.Statement := by
  intro ι _ _ n P D
  refine ⟨fun τ F hF ↦ ?_, fun N _ d g hg r G δ hG τ F hF p q hpq ↦ ?_⟩
  · obtain ⟨d₀, hd₀⟩ := hForms ι n P D
    obtain ⟨g, hg⟩ := hd₀ d₀ le_rfl
    obtain ⟨c₀, hc₀⟩ := P.exists_chart
    have hc₀' : P.IsLive c₀ := hc₀
    let e : ι → ℕ := fun k ↦ ((d₀ k : ℤ) + D.deg k).toNat
    have he : ∀ k, (e k : ℤ) = d₀ k + D.deg k := fun k ↦ Int.toNat_of_nonneg (hg.nonneg k)
    have hge : ∀ c j, IsWeightedHomogeneous (coordDeg n) (g c j) e := by
      intro c j
      obtain ⟨δ', h, hδ'⟩ := hg.homog c j
      have : δ' = e := funext fun k ↦ by have := hδ' k; have := he k; omega
      exact this ▸ h
    have hne : P.mkF (chartMonomial c₀ d₀) ^ τ ≠ 0 := pow_ne_zero _ (SmallSections.mkF_chartMonomial_ne_zero hc₀' d₀)
    refine ⟨{ num := aeval (g c₀) F
              den := chartMonomial c₀ d₀ ^ τ
              numDeg := τ • e
              denDeg := τ • d₀
              num_isHomogeneous := SmallSections.isWeightedHomogeneous_aeval hF (hge c₀)
              den_isHomogeneous := (isWeightedHomogeneous_chartMonomial c₀ d₀).pow τ
              deg_eq := fun k ↦ ?_
              den_not_mem := fun h ↦ hne (by rw [← map_pow]; exact (P.mkF_eq_zero_iff _).mpr h)
              regular := fun c hc ↦ ?_ }, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, he k]
      ring
    · refine ⟨τ • d₀, aeval (g c) F, ⟨τ • e, SmallSections.isWeightedHomogeneous_aeval hF (hge c), fun k ↦ ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, he k]
        ring
      · rw [chartMonomial_nsmul, ← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, map_pow, map_pow,
          SmallSections.mkF_aeval_forms hg hc₀' hF, SmallSections.mkF_aeval_forms hg hc hF]
        ring
    · change P.mkF (aeval (g c₀) F) / P.mkF (chartMonomial c₀ d₀ ^ τ) = _
      rw [SmallSections.mkF_aeval_forms hg hc₀' hF, map_pow, mul_div_cancel_left₀ _ hne]
  · have hfirst : ∀ c : (k : ι) → Fin (n k + 1), P.IsLive c →
        chartMonomial c d ^ τ * p - aeval (g c) F * q ∈ P.ideal := by
      intro c hc
      rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, map_pow, SmallSections.mkF_aeval_forms hg hc hF, hpq]
      ring
    refine ⟨hfirst, fun hsmall z hz ↦ ?_⟩
    obtain ⟨c, hzc⟩ : ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z k (c k) ≠ 0 := by
      have h : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ by
        by_contra h'
        exact hz.1 k (funext fun i ↦ by by_contra hi; exact h' ⟨i, hi⟩)
      choose c hc using h
      exact ⟨c, hc⟩
    have hc : P.IsLive c := SmallSections.isLive_of_mem_points hz hzc
    have hm : evalCone z (chartMonomial c d) ≠ 0 := by
      rw [evalCone_chartMonomial]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)
    have hs := hsmall _ (SmallSections.joinPt_mem_extPoints hg hz hzc)
    rw [SmallSections.plusMetric_joinPt hg N hG hz hzc] at hs
    have heq : evalCone z (chartMonomial c d) ^ τ * evalCone z p =
        eval₂ (Int.castRingHom ℂ) (fun j ↦ evalCone z (g c j)) F * evalCone z q := by
      have h0 := hz.2 _ (hfirst c hc)
      rw [← SmallSections.evalCone_aeval]
      simp only [evalCone, eval₂_sub, eval₂_mul, eval₂_pow, sub_eq_zero] at h0 ⊢
      exact h0
    have hA : ‖evalCone z (chartMonomial c d)‖ ^ τ * ‖evalCone z p‖ =
        ‖eval₂ (Int.castRingHom ℂ) (fun j ↦ evalCone z (g c j)) F‖ * ‖evalCone z q‖ := by
      rw [← norm_pow, ← norm_mul, heq, norm_mul]
    have hle := mul_le_mul_of_nonneg_right hs (norm_nonneg (evalCone z q))
    refine le_of_mul_le_mul_left ?_ (pow_pos (norm_pos_iff.mpr hm) τ)
    calc ‖evalCone z (chartMonomial c d)‖ ^ τ * ‖evalCone z p‖
        = ‖eval₂ (Int.castRingHom ℂ) (D.newPart (D.joinPt z fun j ↦ evalCone z (g c j))) F‖ *
            ‖evalCone z q‖ := hA
      _ ≤ (‖evalCone z (chartMonomial c d)‖ * N.metric z) ^ τ * ‖evalCone z q‖ := hle
      _ = ‖evalCone z (chartMonomial c d)‖ ^ τ * (‖evalCone z q‖ * N.metric z ^ τ) := by ring
end SmallSections
end GroundTheory.Heights₂.Heights
