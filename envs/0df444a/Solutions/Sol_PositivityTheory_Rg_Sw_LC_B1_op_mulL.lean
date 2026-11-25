-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.op_mulL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:15.011852+00:00
-- url     : https://prove2.me/submissions/75f7a80c-ae82-44e1-b6b1-d2ea20fa068e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_opMono_shiftL

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
theorem _root_.solution (μ : σ →₀ ℕ) (s : Sym m n) (f : PX m n) :
    op (monomial (Finsupp.mapDomain Sum.inl μ) 1 * s) f = monomial μ 1 * op s f := by
  conv_lhs => rw [s.as_sum, Finset.mul_sum]
  rw [op_sum]
  conv_rhs => rw [op, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [monomial_mul, one_mul, op_monomial, add_comm, opMono_shiftL, mul_smul_comm]
end PositivityTheory.Rg.Sw.LC.B1
