-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paPoly_Hf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:08:57.079111+00:00
-- url     : https://prove2.me/submissions/e8a11001-0f94-48b3-a9b4-597c2547109b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paPoly_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (a : EuclideanSpace ℂ ι) : (fun v : EuclideanSpace ℂ ι => Hf v a) ∈ paPoly 1 := by
  have h1 : (fun v : EuclideanSpace ℂ ι => Hf v a) =
      ∑ i, (starRingEnd ℂ) (a i) • (fun v : EuclideanSpace ℂ ι => v i) := by
    funext v
    rw [Finset.sum_apply]
    simp only [Hf, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (paPoly_coord i)
end ReciprocityTheory.ChartRestriction.G.I2.FPw
