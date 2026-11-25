-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_integral_smul_mul_eq_toReal_sub_ea92567007f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:36.758823+00:00
-- url     : https://prove2.me/submissions/1f607683-7b33-421e-a6cb-1c10712f3384

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_enorm_mul_eq_ofReal_add_06ddc9c0fdae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)
open scoped ENNReal ComplexOrder
variable {E X W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {f : E → ℝ} (hf : Measurable f) (v : E) {ρ : ℂ → ℝ}
    (hρ : ∀ t, 0 ≤ ρ t) (hρc : Continuous ρ)
    (hp : ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t) ≠ ⊤)
    (hm : ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t) ≠ ⊤) :
    ∫ t : ℂ, f (t • v) * ρ t =
      (∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t)).toReal -
        (∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t)).toReal := by
  have hfv : Measurable fun t : ℂ => f (t • v) :=
    hf.comp (continuous_id.smul continuous_const).measurable
  have hint : Integrable (fun t : ℂ => f (t • v) * ρ t) := by
    refine ⟨(hfv.mul hρc.measurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ t : ℂ, ‖f (t • v) * ρ t‖ₑ
        = ∫⁻ t : ℂ, (ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t) +
            ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t)) :=
          lintegral_congr fun t => enorm_mul_eq_ofReal_add (hρ t)
      _ = (∫⁻ t : ℂ, ENNReal.ofReal (f (t • v)) * ENNReal.ofReal (ρ t)) +
            ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v)) * ENNReal.ofReal (ρ t) :=
          lintegral_add_left ((ENNReal.measurable_ofReal.comp hfv).mul
            (ENNReal.measurable_ofReal.comp hρc.measurable)) _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hp.lt_top, hm.lt_top⟩
  have key : ∀ (a : ℝ) (t : ℂ), ENNReal.ofReal (a * ρ t) = ENNReal.ofReal a * ENNReal.ofReal (ρ t) :=
    fun a t => ENNReal.ofReal_mul' (hρ t)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  simp_rw [← neg_mul, key]
end GroundTheory.Heights₂.Heights
