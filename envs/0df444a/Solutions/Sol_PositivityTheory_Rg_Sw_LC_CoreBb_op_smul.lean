-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.op_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:24.00113+00:00
-- url     : https://prove2.me/submissions/d13a7419-bc01-45fc-a9a7-03611abddf52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_add
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
theorem _root_.solution (a : ℂ) (s : Sym m n) (f : PX m n) : op (a • s) f = a • op s f := by
  induction s using MvPolynomial.induction_on' with
  | monomial t c => rw [smul_monomial, op_monomial, op_monomial, smul_eq_mul, mul_smul]
  | add p q hp hq => rw [smul_add, op_add, op_add, hp, hq, smul_add]
end PositivityTheory.Rg.Sw.LC.CoreBb
