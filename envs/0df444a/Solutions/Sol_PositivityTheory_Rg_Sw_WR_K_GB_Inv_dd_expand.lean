-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.dd_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:42.011239+00:00
-- url     : https://prove2.me/submissions/e71cc203-3d50-49ed-a360-bb7b651532d6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_eq_sum_E

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
theorem _root_.solution (H : Mc n) (f : Mc n → ℂ) (x : Mc n) :
    dd H f x = ∑ p : Fin n × Fin n, H p.1 p.2 * dd (E p) f x := by
  conv_lhs => rw [eq_sum_E H]
  simp [dd, map_sum, map_smul]
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
