-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.ph_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:27.239555+00:00
-- url     : https://prove2.me/submissions/a7ef0003-bb23-419f-8e36-267beae65623

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_Intw_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_Iso_mul
import Theorems.Thm_PositivityTheory_ThKR_LL_temperate_quad
import Theorems.Thm_GlobalTheory_Published_Metaplectic_eChar_apply
import Theorems.Thm_GlobalTheory_Published_Metaplectic_hasTemperateGrowth_eChar
import Theorems.Thm_PositivityTheory_ThKR_LL_LD_const
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
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution (S : Eu l →L[ℝ] Eu l) (f : Sch l) (x : Eu l) :
    ph S f x = exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) * f x := by
  have h2 : Function.HasTemperateGrowth fun x : Eu l => (-2⁻¹ : ℝ) * ⟪x, S x⟫ :=
    (Function.HasTemperateGrowth.const _).mul (temperate_quad S)
  have h3 : Function.HasTemperateGrowth fun x : Eu l => exp (((-π * ⟪x, S x⟫ : ℝ) : ℂ) * I) := by
    convert GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp h2 using 1
    funext x
    simp only [Function.comp, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  rw [ph, smulLeftCLM_apply_apply h3, smul_eq_mul]
end PositivityTheory.ThKR.LL
