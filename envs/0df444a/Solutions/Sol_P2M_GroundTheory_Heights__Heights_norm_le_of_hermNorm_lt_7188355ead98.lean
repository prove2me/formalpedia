-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_norm_le_of_hermNorm_lt_7188355ead98
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:41.791841+00:00
-- url     : https://prove2.me/submissions/64367518-1230-433c-b6f8-5980c78c0f3e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open Matrix
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) {v : Fin n → ℂ} (hv : h.norm v < 1) (j : Fin n) :
    ‖v j‖ ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ := by
  have hinv : h.mat⁻¹ * h.mat = 1 := Matrix.nonsing_inv_mul _ h.isUnit_det
  have hv' : v = h.mat⁻¹ *ᵥ (h.mat *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hcoord : ∀ l, ‖(h.mat *ᵥ v) l‖ ≤ 1 := by
    intro l
    have h1 : ‖(h.mat *ᵥ v) l‖ ^ 2 ≤ ∑ m, ‖(h.mat *ᵥ v) m‖ ^ 2 :=
      Finset.single_le_sum (f := fun m => ‖(h.mat *ᵥ v) m‖ ^ 2) (fun m _ => sq_nonneg _)
        (Finset.mem_univ l)
    have h2 : √(‖(h.mat *ᵥ v) l‖ ^ 2) ≤ h.norm v := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq (norm_nonneg _)] at h2
    linarith
  calc ‖v j‖ = ‖(h.mat⁻¹ *ᵥ (h.mat *ᵥ v)) j‖ := by rw [← hv']
    _ = ‖∑ l, h.mat⁻¹ j l * (h.mat *ᵥ v) l‖ := rfl
    _ ≤ ∑ l, ‖h.mat⁻¹ j l * (h.mat *ᵥ v) l‖ := norm_sum_le _ _
    _ ≤ ∑ l, ‖h.mat⁻¹ j l‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hcoord l)
    _ ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
        Finset.single_le_sum (f := fun j' => ∑ l, ‖h.mat⁻¹ j' l‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
end GroundTheory.Heights₂.Heights
