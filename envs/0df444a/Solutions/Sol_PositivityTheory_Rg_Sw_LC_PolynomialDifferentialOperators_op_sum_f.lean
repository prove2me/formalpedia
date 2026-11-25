-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.op_sum_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:59:50.237836+00:00
-- url     : https://prove2.me/submissions/615fd16a-830a-468c-bc5e-3f1cb5df7db8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FirstFamilySymbolMulVariablePow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainInlInr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_add_f
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_smul_f
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_op_zero_f


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
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
theorem _root_.solution (u : Sym m n) {ι : Type*} (S : Finset ι) (c : ι → ℂ) (h : ι → PX m n) :
    op u (∑ i ∈ S, c i • h i) = ∑ i ∈ S, c i • op u (h i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [op_zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add_f, op_smul_f, ih]
end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
