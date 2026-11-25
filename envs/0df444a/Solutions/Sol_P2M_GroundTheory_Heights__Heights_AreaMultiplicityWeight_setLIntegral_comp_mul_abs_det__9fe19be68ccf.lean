-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaMultiplicityWeight_setLIntegral_comp_mul_abs_det__9fe19be68ccf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:34.990643+00:00
-- url     : https://prove2.me/submissions/69c9831e-7614-4ba0-9502-19e1d9fc75a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaMultiplicityWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight

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
open MeasureTheory Module Set Filter Function
open scoped ENNReal NNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace AreaMultiplicityWeight
theorem _root_.solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : NullMeasurableSet s μ) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in s, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ = ∫⁻ y in f '' s, g y ∂μ := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have himg : f '' t =ᵐ[μ] f '' s := by
    have hst : s = t ∪ (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [hst, image_union]
    refine (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ (fun x hx ↦ ?_)
      (ae_eq_set.1 t_eq_s).2
    exact (hf' x hx.1).differentiableWithinAt.mono sdiff_subset
  rw [setLIntegral_congr t_eq_s.symm, ← setLIntegral_congr himg,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ ht (fun x hx => (hf' x (ts hx)).mono ts)
      (hf.mono ts)]
  congr 1
  funext x
  exact mul_comm _ _
end AreaMultiplicityWeight
end GroundTheory.Heights₂.Heights
