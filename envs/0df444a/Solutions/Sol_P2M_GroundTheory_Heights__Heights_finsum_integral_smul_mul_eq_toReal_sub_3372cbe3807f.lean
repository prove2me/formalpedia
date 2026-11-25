-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finsum_integral_smul_mul_eq_toReal_sub_3372cbe3807f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:36.761811+00:00
-- url     : https://prove2.me/submissions/520d1d11-a461-4e73-9829-0fb53dbf5da8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_smul_mul_eq_toReal_sub_ea92567007f9

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
theorem _root_.solution {f : E → ℝ} (hf : Measurable f) {T : Set W}
    (hT : T.Finite) (v : W → E) (ρ : W → ℂ → ℝ) (hρ : ∀ w t, 0 ≤ ρ w t)
    (hρc : ∀ w, Continuous (ρ w))
    (hp : ∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v w)) * ENNReal.ofReal (ρ w t) ≠ ⊤)
    (hm : ∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v w)) * ENNReal.ofReal (ρ w t) ≠ ⊤) :
    ∑ᶠ w ∈ T, ∫ t : ℂ, f (t • v w) * ρ w t =
      (∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (f (t • v w)) * ENNReal.ofReal (ρ w t)).toReal -
        (∑ᶠ w ∈ T, ∫⁻ t : ℂ, ENNReal.ofReal (-f (t • v w)) * ENNReal.ofReal (ρ w t)).toReal := by
  simp only [finsum_mem_eq_finite_toFinset_sum _ hT] at hp hm ⊢
  have hp' := fun w (hw : w ∈ hT.toFinset) =>
    ne_top_of_le_ne_top hp (Finset.single_le_sum (fun _ _ => zero_le) hw)
  have hm' := fun w (hw : w ∈ hT.toFinset) =>
    ne_top_of_le_ne_top hm (Finset.single_le_sum (fun _ _ => zero_le) hw)
  rw [ENNReal.toReal_sum hp', ENNReal.toReal_sum hm', ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun w hw =>
    integral_smul_mul_eq_toReal_sub hf (v w) (hρ w) (hρc w) (hp' w hw) (hm' w hw)
end GroundTheory.Heights₂.Heights
