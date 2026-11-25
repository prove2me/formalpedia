-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.torusMean_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:33:45.453816+00:00
-- url     : https://prove2.me/submissions/87eea293-2918-4063-8ff3-fa51b836ceb1

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanD
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMean
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integral_log_circ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_log_norm_coeff_bot_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_log_norm_coeff_top_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurable_tmLog
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_norm_torusPoint
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tmLog_update
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tmSlice_coeff
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tm_ae_ne
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tm_int
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tm_integrable_comp
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tm_integral_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : TorusMeanBasicStatement ∧ TorusCoeffStatement := by
  classical
  refine ⟨fun ι _ => ⟨fun f _ => tm_int f, fun f g hf hg => ?_, fun s c => ?_⟩,
    fun ι _ f i k hk hext => ?_⟩
  · show ∫ θ, tmLog (f * g) θ ∂(torusProb ι) =
      ∫ θ, tmLog f θ ∂(torusProb ι) + ∫ θ, tmLog g θ ∂(torusProb ι)
    rw [← integral_add (tm_int f) (tm_int g)]
    apply integral_congr_ae
    filter_upwards [tm_ae_ne f hf, tm_ae_ne g hg] with θ h1 h2
    simp only [tmLog, map_mul, norm_mul]
    exact Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)
  · have hm : ∀ θ, tmLog (MvPolynomial.monomial s c) θ = Real.log ‖c‖ := by
      intro θ
      simp [tmLog, MvPolynomial.eval_monomial, Finsupp.prod, norm_prod, norm_pow,
        norm_torusPoint]
    show ∫ θ, tmLog (MvPolynomial.monomial s c) θ ∂(torusProb ι) = Real.log ‖c‖
    simp_rw [hm]
    simp
  · show ∫ θ, tmLog (coeffIn i k f) θ ∂(torusProb ι) ≤ ∫ θ, tmLog f θ ∂(torusProb ι)
    have hFi : Integrable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) :=
      (tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable).mpr (tm_int f)
    rw [tm_integral_comp i (measurable_tmLog f).aestronglyMeasurable,
      integral_prod (fun p => tmLog f (tmUpd i p)) hFi]
    refine integral_mono_ae (tm_int _) hFi.integral_prod_left ?_
    filter_upwards [tm_ae_ne _ hk] with θ hθ
    show tmLog (coeffIn i k f) θ ≤ ∫ t, tmLog f (update θ i t) ∂unitIntervalMeasure
    simp_rw [tmLog_update]
    rw [integral_log_circ]
    have hc : (tmSlice i (torusPoint θ) f).coeff k = MvPolynomial.eval (torusPoint θ) (coeffIn i k f) :=
      tmSlice_coeff i _ f k
    have hk' : (tmSlice i (torusPoint θ) f).coeff k ≠ 0 := hc ▸ hθ
    show Real.log ‖MvPolynomial.eval (torusPoint θ) (coeffIn i k f)‖ ≤ _
    rw [← hc]
    rcases hext with htop | hbot
    · exact log_norm_coeff_top_le _ k hk' fun k' hk'' => by
        rw [tmSlice_coeff, htop k' hk'', map_zero]
    · exact log_norm_coeff_bot_le _ k hk' fun k' hk'' => by
        rw [tmSlice_coeff, hbot k' hk'', map_zero]
end ReciprocityTheory.MultiplicativeHeights
