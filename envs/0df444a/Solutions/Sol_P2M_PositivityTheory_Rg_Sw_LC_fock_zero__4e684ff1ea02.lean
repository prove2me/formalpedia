-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LC_fock_zero__4e684ff1ea02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:51.406738+00:00
-- url     : https://prove2.me/submissions/2d1062a7-54db-40e8-bd9e-974fd5e00962

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_fL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
variable (hB : FockBasic)
include hB
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution {c : ℝ} (hc : 0 < c) : fock c (0 : PX m n) = 0 := by
  rw [← fL_apply hB hc, map_zero]
end PositivityTheory.Rg.Sw.LC
