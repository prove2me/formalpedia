-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.alt_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:34:02.82952+00:00
-- url     : https://prove2.me/submissions/ac939af1-54ea-42ef-98ee-415d05143d06

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
import Theorems.Thm_PositivityTheory_Rg_Cz_alt_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.PStepFormula
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.PStepFormula
theorem _root_.solution {X : Type} [AddCommGroup X] [Module ℂ X] (g : TV n X (Fin n)) (J : Fin n → Fin n) (a b : Fin n)
    (h : a ≠ b) : alt Finset.univ g (J ∘ Equiv.swap a b) = -alt Finset.univ g J := by
  rw [alt_apply, alt_apply, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap a b)) _ _ fun σ => ?_
  have h1 : J ∘ ⇑(Equiv.swap a b * σ) = (J ∘ Equiv.swap a b) ∘ σ := by
    funext x; simp
  simp only [Equiv.coe_mulLeft, h1, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h]
  push_cast
  rw [neg_one_mul, neg_smul, neg_neg]
end PositivityTheory.Rg.Cz.PStepFormula
