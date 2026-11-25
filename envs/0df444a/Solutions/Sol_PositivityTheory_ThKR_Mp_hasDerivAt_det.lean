-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.hasDerivAt_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:43.414752+00:00
-- url     : https://prove2.me/submissions/7649abb3-56aa-48a4-a58f-1f7acef2bd2b

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_hasDerivAt
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution (P K : Matrix l l ℂ) (t₀ : ℝ) (hP : (P + (t₀ : ℂ) • K).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (P + (t : ℂ) • K).det)
      ((P + (t₀ : ℂ) • K).det * ((P + (t₀ : ℂ) • K)⁻¹ * K).trace) t₀ := by
  have hu : IsUnit (P + (t₀ : ℂ) • K).det := hP.isUnit
  have e : ∀ t : ℝ, (P + (t : ℂ) • K).det = (P + (t₀ : ℂ) • K).det *
      (1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * ((t - t₀ : ℝ) : ℂ) +
        (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval
          ((t - t₀ : ℝ) : ℂ) * ((t - t₀ : ℝ) : ℂ) ^ 2) := fun t => by
    rw [← Matrix.det_one_add_smul, ← Matrix.det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ofReal_sub, sub_smul]
    congr 1
    abel
  have hφ : HasDerivAt (fun z : ℂ => 1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * z +
      (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval z * z ^ 2)
      ((P + (t₀ : ℂ) • K)⁻¹ * K).trace ((t₀ - t₀ : ℝ) : ℂ) := by
    have := (((hasDerivAt_id (0 : ℂ)).const_mul ((P + (t₀ : ℂ) • K)⁻¹ * K).trace).const_add 1).add
      ((Polynomial.hasDerivAt (det (1 + (Polynomial.X : Polynomial ℂ) •
        ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX (0 : ℂ)).mul ((hasDerivAt_id (0 : ℂ)).pow 2))
    rw [sub_self, ofReal_zero]
    exact (this.congr_deriv (by simp)).congr_of_eventuallyEq (.of_forall fun z => by simp)
  have hh : HasDerivAt (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)) 1 t₀ := by
    simpa using ((hasDerivAt_id t₀).sub_const t₀).ofReal_comp
  have := (hφ.comp t₀ hh).const_mul (P + (t₀ : ℂ) • K).det
  rw [mul_one] at this
  exact this.congr_of_eventuallyEq (.of_forall e)
end PositivityTheory.ThKR.Mp
