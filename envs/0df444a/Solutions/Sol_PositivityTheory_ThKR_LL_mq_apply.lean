-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.mq_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:41.057686+00:00
-- url     : https://prove2.me/submissions/2231ddaa-6004-4df0-a9a6-920a3f282c2b

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_const
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_temperate_quad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution (S : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) : mq S f x = ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I * f x := by
  have h2 : Function.HasTemperateGrowth fun x : Eu l => -π * ⟪x, S x⟫ :=
    (Function.HasTemperateGrowth.const _).mul (temperate_quad S)
  have h3 : Function.HasTemperateGrowth fun x : Eu l => ((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I :=
    (ofRealCLM.hasTemperateGrowth.comp h2).mul (Function.HasTemperateGrowth.const _)
  rw [mq, smulLeftCLM_apply_apply h3, smul_eq_mul]
end PositivityTheory.ThKR.LL
