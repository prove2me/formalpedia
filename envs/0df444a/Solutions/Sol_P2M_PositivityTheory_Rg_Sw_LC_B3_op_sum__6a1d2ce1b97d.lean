-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LC_B3_op_sum__6a1d2ce1b97d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:52.970133+00:00
-- url     : https://prove2.me/submissions/6e42be25-8d91-44ef-9c53-c146e4117c60

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_zero


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B3
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.B3
theorem _root_.solution {ι : Type*} (T : Finset ι) (u : ι → Sym m n) (f : PX m n) :
    op (∑ i ∈ T, u i) f = ∑ i ∈ T, op (u i) f := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [op_zero]
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add, ih]
end PositivityTheory.Rg.Sw.LC.B3
