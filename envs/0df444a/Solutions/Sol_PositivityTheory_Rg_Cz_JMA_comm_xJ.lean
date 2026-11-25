-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.comm_xJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:25.189172+00:00
-- url     : https://prove2.me/submissions/8e5fba7e-c187-4ff3-af19-7e0a070868b5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_xJ_eq
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_eAt_eq_sub
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
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m) (X : Module.End ℂ (TV n M (Fin m)))
    (h1 : ∀ a b, Commute X (tE (Finset.univ.filter (· < j)) E a b))
    (h2 : ∀ a b, Commute X (tE (insert j (Finset.univ.filter (· < j))) E a b)) : Commute X (xJ E j) := by
  rw [xJ_eq]
  refine Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => (h1 a b).mul_right ?_
  rw [eAt_eq_sub (Finset.univ.filter (· < j)) j (by simp) E]
  exact (h2 b a).sub_right (h1 b a)
end PositivityTheory.Rg.Cz.JMA
