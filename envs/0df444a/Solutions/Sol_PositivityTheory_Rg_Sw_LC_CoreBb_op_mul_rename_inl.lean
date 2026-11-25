-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.op_mul_rename_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:05.865916+00:00
-- url     : https://prove2.me/submissions/37f1a6fd-fe4d-480d-97d8-2a0c2c55b571

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_mul_X_inl

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
theorem _root_.solution (s : Sym m n) (g f : PX m n) :
    op (s * rename Sum.inl g) f = g * op s f := by
  induction g using MvPolynomial.induction_on generalizing s with
  | C a => rw [rename_C, mul_comm, C_mul', op_smul, smul_eq_C_mul]
  | add p q hp hq => rw [map_add, mul_add, op_add, hp, hq, add_mul]
  | mul_X p k hp => rw [map_mul, rename_X, ← mul_assoc, op_mul_X_inl, hp]; ring
end PositivityTheory.Rg.Sw.LC.CoreBb
