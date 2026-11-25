-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_smul_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:40.807159+00:00
-- url     : https://prove2.me/submissions/9b5a6a58-82db-4a77-9b7a-0e6c7bce76b5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_opMono_smul

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
theorem _root_.solution (u : Sym m n) (a : ℂ) (f : PX m n) : op u (a • f) = a • op u f := by
  simp only [op, opMono_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_comm]
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
