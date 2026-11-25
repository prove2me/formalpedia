-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.isUnit_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:40.236844+00:00
-- url     : https://prove2.me/submissions/3521d6a9-4997-4183-8cc6-a4c9e183e64a

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_dil_one
import Theorems.Thm_PositivityTheory_ThKR_LL_dil_mul

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
theorem _root_.solution {B : Eu l →L[ℝ] Eu l} (h : IsUnit B) : IsUnit (dil B) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨⟨dil u, dil (u⁻¹ : (Eu l →L[ℝ] Eu l)ˣ), by rw [dil_mul u.isUnit u⁻¹.isUnit, Units.inv_mul, dil_one],
    by rw [dil_mul u⁻¹.isUnit u.isUnit, Units.mul_inv, dil_one]⟩, rfl⟩
end PositivityTheory.ThKR.LL
