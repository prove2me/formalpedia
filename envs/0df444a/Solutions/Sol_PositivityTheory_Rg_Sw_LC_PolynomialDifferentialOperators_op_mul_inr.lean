-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_mul_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:08.810617+00:00
-- url     : https://prove2.me/submissions/2a7556e3-1b13-4058-ba95-141232e2928d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_opMono_add_inr

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
theorem _root_.solution (u : Sym m n) (k : Ix m n) (f : PX m n) : op (u * X (Sum.inr k)) f = op u (pderiv k f) := by
  classical
  conv_lhs => rw [u.as_sum, Finset.sum_mul]
  rw [op_sum]
  conv_rhs => rw [op]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [X, monomial_mul, mul_one, op_monomial, opMono_add_inr]
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
