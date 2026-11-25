-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.continuous_kr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:25.8108+00:00
-- url     : https://prove2.me/submissions/619ba6b0-de55-4de6-b5f1-85b42997fc29

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_norm_cexp_It
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_continuous_ip
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_continuous_gam
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_integrable_gauss


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (ε t : ℝ) (hε : 0 < ε) : Continuous (kr (n := n) ε t) := by
  unfold kr
  refine continuous_of_dominated (bound := fun y => ‖gam (n := n) ε y‖) ?_ ?_
    (integrable_gauss ε hε).norm ?_
  · intro u
    exact ((continuous_gam ε).mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ip.comp (continuous_id.prodMk continuous_const)))))).aestronglyMeasurable
  · intro u; refine Eventually.of_forall fun y => ?_
    rw [norm_mul, norm_cexp_It, mul_one]
  · refine Eventually.of_forall fun y => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ip.comp (continuous_const.prodMk continuous_id)))))
end PositivityTheory.Rg.Sw.WR.D.Moll
