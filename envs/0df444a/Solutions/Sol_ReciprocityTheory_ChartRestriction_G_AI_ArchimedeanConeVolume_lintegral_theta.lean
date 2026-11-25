-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:14.701527+00:00
-- url     : https://prove2.me/submissions/aad226c1-9c86-4b47-b0aa-4570101632fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
theorem _root_.solution (G : ℝ → ℝ≥0∞) :
    ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (sin θ) * G (cos θ) = ∫⁻ t in Ioo (-1 : ℝ) 1, G t := by
  have h1 : ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (sin θ) * G (cos θ) =
      ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (sin θ) * G (cos θ) := by
    rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext θ
    by_cases h0 : θ ∈ Ioo 0 π
    · have : θ ∈ Ioo (-π) π := ⟨by linarith [h0.1, pi_pos], h0.2⟩
      simp [indicator_of_mem h0, indicator_of_mem this]
    · rw [indicator_of_notMem h0]
      by_cases h1 : θ ∈ Ioo (-π) π
      · rw [indicator_of_mem h1]
        have hθ : θ ≤ 0 := by
          by_contra h
          exact h0 ⟨lt_of_not_ge h, h1.2⟩
        have : sin θ ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le hθ h1.1.le
        simp [ENNReal.ofReal_of_nonpos this]
      · rw [indicator_of_notMem h1]
  have h2 : cos '' Ioo 0 π = Ioo (-1 : ℝ) 1 := cosPartialHomeomorph.image_source_eq_target
  rw [h1, ← h2, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (f' := fun x => -sin x) (fun x _ => (hasDerivAt_cos x).hasDerivWithinAt)
    (injOn_cos.mono Ioo_subset_Icc_self)]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  rw [abs_neg, abs_of_pos (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)]
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
