-- Prove2me | solution 1 for ZetaZeros.D.EllReg.lintegral_dil_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:09:55.721039+00:00
-- url     : https://prove2.me/submissions/3d19f157-f94c-4baa-bf6e-231bed2ac9b2

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace ZetaZeros.D.EllReg
theorem _root_.solution (r : ℝ) (hr : 0 < r) (D : ℝ) (hD : (Module.finrank ℝ V : ℝ) < D) :
    (∫⁻ w : V, ENNReal.ofReal (r ^ Module.finrank ℝ V * (1 + ‖r • w‖) ^ (-D))) =
      ∫⁻ w : V, ENNReal.ofReal ((1 + ‖w‖) ^ (-D)) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hmeas : Measurable (fun w : V => r • w) := measurable_const_smul r
  have hg : Measurable (fun u : V => ENNReal.ofReal ((1 + ‖u‖) ^ (-D))) := by fun_prop
  have h1 : ∀ w : V, ENNReal.ofReal (r ^ Module.finrank ℝ V * (1 + ‖r • w‖) ^ (-D)) =
      ENNReal.ofReal (r ^ Module.finrank ℝ V) * ENNReal.ofReal ((1 + ‖r • w‖) ^ (-D)) :=
    fun w => ENNReal.ofReal_mul (by positivity)
  simp_rw [h1]
  have hg' : Measurable (fun w : V => ENNReal.ofReal ((1 + ‖r • w‖) ^ (-D))) := hg.comp hmeas
  rw [MeasureTheory.lintegral_const_mul _ hg']
  rw [← MeasureTheory.lintegral_map hg hmeas, MeasureTheory.Measure.map_addHaar_smul _ hr0,
    MeasureTheory.lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
end ZetaZeros.D.EllReg
