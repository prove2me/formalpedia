-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:21:48.662883+00:00
-- url     : https://prove2.me/submissions/60713dc3-20c1-4fe2-a307-ba0342ddc58f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_fund
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_per_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution : StepT := by
  intro E _ _ X n F _ _ _ g hg hper a
  rw [setAverage_eq, setAverage_eq]
  congr 1
  have h1 := (measurePreserving_add_right (volume : Measure (Fin n → Vsp X.dim)) a).setIntegral_preimage_emb
    (measurableEmbedding_addRight a) (fun v => g (v - a)) (X.fd n)
  simp only [add_sub_cancel_right] at h1
  rw [← h1]
  exact (fd_trans X n a).setIntegral_eq (fd_fund X n) (per_span X n g hper)
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
