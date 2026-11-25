-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:06.874647+00:00
-- url     : https://prove2.me/submissions/b22a8b7a-11ee-4cab-8915-02f8a714d61a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ComapDomainInlAdd
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_opMono_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_dvE_zero

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
theorem _root_.solution (a : ℂ) (f : PX m n) : op (C a : Sym m n) f = a • f := by
  rw [← monomial_zero', op_monomial, opMono_eq]
  have h0 : (fun k : Ix m n => (0 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) = 0 := by ext; simp
  rw [h0, dvE_zero, Finsupp.comapDomain_zero]
  simp
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
