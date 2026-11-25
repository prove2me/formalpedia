-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreD.rr_Om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:33.780801+00:00
-- url     : https://prove2.me/submissions/953f5821-b3f1-46a8-9141-7c01322f5931

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BoxLeFirstFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_op_sum_sym
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_box_le_first_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_symK_mem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_symbol_first_family_of_mem


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreD
variable {m n : ℕ} {ε : Fin m → Bool}
variable (R : Set (Fin m → ℕ)) (hV : ∀ (i j : Fin n), ∀ f ∈ box ε R, KopL ε i j f ∈ box ε R)
variable (hS : SymKComm)
include hS
namespace PositivityTheory.Rg.Sw.LC.CoreD
theorem _root_.solution (N : ℕ) (x : S (n := n) ε N) : rr R N (OmS ε N x) = OmH R hV (rr R N x) := by
  refine LinearMap.ext fun f => ?_
  have hf : f.1 ∈ F1 ε := box_le_first_family R f.2
  have hF1 : ∀ (i j : Fin n) (g : box (n := n) ε R), (KopL ε i j g.1) ∈ F1 ε := fun i j g => box_le_first_family R (hV i j g.1 g.2)
  simp only [rr, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, Submodule.coe_subtype, OmH,
    LinearMap.sum_apply, Module.End.mul_apply, opL]
  change op (Om ε x.1) f.1 = _
  rw [Om_apply, op_sum_sym]
  refine Finset.sum_congr rfl fun ij _ => ?_
  have hx : SymbolInFirstFamily ε x.1 := symbol_first_family_of_mem x.2
  have hx' : SymbolInFirstFamily ε (symK ε ij.2 ij.1 x.1) := symbol_first_family_of_mem (symK_mem _ _ x.2)
  rw [hS m n ε ij.1 ij.2 _ hx' f.1 hf, hS m n ε ij.2 ij.1 _ hx f.1 hf,
    hS m n ε ij.2 ij.1 _ hx _ (hF1 ij.1 ij.2 f)]
  rfl
end PositivityTheory.Rg.Sw.LC.CoreD
