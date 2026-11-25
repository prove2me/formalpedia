-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.op_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:44.992073+00:00
-- url     : https://prove2.me/submissions/9be6ed61-cd9a-4372-bd4c-ea1bc412c8ea

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_Dfun_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_opMono_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_monomial

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreBb
theorem _root_.solution (a : ℂ) (f : PX m n) : op (C a : Sym m n) f = a • f := by
  rw [← monomial_zero', op_monomial, opMono_eq]
  simp [Dfun_zero]
end PositivityTheory.Rg.Sw.LC.CoreBb
