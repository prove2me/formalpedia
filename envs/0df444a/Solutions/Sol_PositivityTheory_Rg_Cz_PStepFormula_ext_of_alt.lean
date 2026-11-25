-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.ext_of_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:36:28.511809+00:00
-- url     : https://prove2.me/submissions/b7d07449-74e0-439c-94fa-4a797a53973b

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
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℂ W] {X Y : Module.End ℂ W}
    (h : (lift X : Module.End ℂ (TV n W (Fin n))) * alt Finset.univ = lift Y * alt Finset.univ) : X = Y := by
  classical
  ext w
  let g : TV n W (Fin n) := fun J => if J = id then w else 0
  have hg : alt Finset.univ g id = w := by
    rw [alt_apply, Finset.sum_eq_single 1]
    · simp [g]
    · intro σ _ hσ
      have hs : (id ∘ ⇑σ) ≠ id := fun h' => hσ (Equiv.ext fun x => congrFun h' x)
      simp only [g, if_neg hs, smul_zero]
    · simp
  have := congrArg (fun T : Module.End ℂ (TV n W (Fin n)) => T g id) h
  simpa only [Module.End.mul_apply, lift_apply, hg] using this
end PositivityTheory.Rg.Cz.PStepFormula
