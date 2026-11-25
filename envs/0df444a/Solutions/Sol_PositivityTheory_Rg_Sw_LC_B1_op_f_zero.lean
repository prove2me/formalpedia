-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.op_f_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:08.114839+00:00
-- url     : https://prove2.me/submissions/11783d77-8fc4-4e27-bec3-fb2d0a32e0e3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_opMono_zero

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
namespace PositivityTheory.Rg.Sw.LC.B1
theorem _root_.solution (s : Sym m n) : op s (0 : PX m n) = 0 := by
  unfold op; exact Finset.sum_eq_zero fun t _ => by rw [opMono_zero, smul_zero]
end PositivityTheory.Rg.Sw.LC.B1
