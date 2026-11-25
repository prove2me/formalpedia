-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.actT_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:40.425117+00:00
-- url     : https://prove2.me/submissions/b53ce34a-c3a7-4cb8-adb6-91fc638c0ba4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_eq
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_Aop_one
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TGK
theorem _root_.solution {ι Γ : Type} [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ, κ τ 1 = 1) (hρ : ρ 1 = 1) : actT lab κ ρ 1 = 1 := by
  rw [actT_eq]
  simp only [hκ, hρ, Aop_one, mul_one]
  rfl
end PositivityTheory.Rg.Cz.TGK
