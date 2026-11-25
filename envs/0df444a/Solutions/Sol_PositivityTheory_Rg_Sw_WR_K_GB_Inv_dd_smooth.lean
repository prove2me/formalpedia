-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.dd_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:20.761186+00:00
-- url     : https://prove2.me/submissions/0c8d95a5-e425-4e11-b3ed-ce858a7c20fa

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_top_succ_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv
namespace PositivityTheory.Rg.Sw.WR.K.GB.Inv
theorem _root_.solution {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    (H : Mc n) : ContDiffOn ℂ (⊤ : ℕ∞) (dd H F) U :=
  (hF.fderiv_of_isOpen hU top_succ_le).clm_apply contDiffOn_const
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
