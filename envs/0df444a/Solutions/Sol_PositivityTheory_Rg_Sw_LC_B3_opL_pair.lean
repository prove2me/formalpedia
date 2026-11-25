-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B3.opL_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:23:56.232507+00:00
-- url     : https://prove2.me/submissions/e2f42d89-f6fd-4f53-badb-edff51bf5e6b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_op_X_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_op_X_inr
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_B3_op_sum__6a1d2ce1b97d
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_CoreBb_pderiv_comm__c7d947a11a2b
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_eq_opL
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_mul_X_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_mul_X_inr


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
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) (hc : c ≠ 0) (a b : Fin m) :
    ∃ κ : ℂ, opL (pairSym (n := n) ε a b) = κ • firstFamilyOperatorEnd ε c a b := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have key : ∀ f, opL (pairSym (n := n) ε a b) f = ∑ i : Fin n, op (vecVar ε a i * covVar ε b i) f := by
    intro f
    rw [← op_eq_opL]
    exact op_sum' _ _ f
  cases ha : ε a <;> cases hb : ε b
  · refine ⟨1, LinearMap.ext fun f => ?_⟩
    rw [key]
    simp [firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]
  · refine ⟨1 / (2 * (c : ℂ)), LinearMap.ext fun f => ?_⟩
    rw [key]
    simp [firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]
    rw [smul_smul, show ((c : ℂ)⁻¹ * 2⁻¹) * (2 * c) = 1 by field_simp, one_smul]
    exact Finset.sum_congr rfl fun i _ => pderiv_comm' _ _ f
  · refine ⟨-(2 * (c : ℂ)), LinearMap.ext fun f => ?_⟩
    rw [key]
    simp [firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]
    rw [smul_smul, show (2 * (c : ℂ)) * ((c : ℂ)⁻¹ * 2⁻¹) = 1 by field_simp, one_smul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · refine ⟨-1, LinearMap.ext fun f => ?_⟩
    rw [key]
    simp [firstFamilyOperatorEnd, D1, vecVar, covVar, ha, hb, op_mul_X_inl, op_mul_X_inr, op_X_inl, op_X_inr]
end PositivityTheory.Rg.Sw.LC.B3
