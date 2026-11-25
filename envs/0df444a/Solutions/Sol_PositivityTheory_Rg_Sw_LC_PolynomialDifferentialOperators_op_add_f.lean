-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_add_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:49.274321+00:00
-- url     : https://prove2.me/submissions/63af91cc-b2a3-4e48-a95a-9f70c9a3ecf5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_opMono_add

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
theorem _root_.solution (u : Sym m n) (f g : PX m n) : op u (f + g) = op u f + op u g := by
  simp only [op, opMono_add, smul_add, Finset.sum_add_distrib]
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
