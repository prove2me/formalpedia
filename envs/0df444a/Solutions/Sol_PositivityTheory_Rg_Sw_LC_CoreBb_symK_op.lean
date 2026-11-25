-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.symK_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:08:47.495938+00:00
-- url     : https://prove2.me/submissions/f36f0352-84e8-4cf6-a117-5efcf95dbe86

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_neg
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_C
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_neg_f
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_sub_f
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_zero_f
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_mul_X_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_mul_X_inr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_mul_rename_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_KopL_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_KopL_pderiv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_symK_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_symK_inr

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (s : Sym m n) :
    ∀ f : PX m n, op (symK ε i j s) f = KopL ε i j (op s f) - op s (KopL ε i j f) := by
  induction s using MvPolynomial.induction_on with
  | C a =>
    intro f
    rw [MvPolynomial.derivation_C, op_zero, op_C, op_C, map_smul, sub_self]
  | add p q hp hq =>
    intro f
    rw [map_add, op_add, hp, hq, op_add, op_add, map_add]
    abel
  | mul_X p k hp =>
    intro f
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, op_add, mul_comm (X k) (symK ε i j p)]
    cases k with
    | inl k =>
      rw [symK_inl, op_mul_rename_inl, op_mul_X_inl, hp, op_mul_X_inl, op_mul_X_inl, KopL_mul]
      ring
    | inr k =>
      rw [op_mul_X_inr, hp, op_mul_X_inr, op_mul_X_inr]
      have key : op (p * symK ε i j (X (Sum.inr k))) f =
          op p (KopL ε i j (pderiv k f)) - op p (pderiv k (KopL ε i j f)) := by
        rw [← op_sub_f, KopL_pderiv, symK_inr]
        split_ifs <;> simp [mul_neg, op_neg, op_mul_X_inr, op_neg_f, op_zero_f, op_zero]
      rw [key]
      abel
end PositivityTheory.Rg.Sw.LC.CoreBb
