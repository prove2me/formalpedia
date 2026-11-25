-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.actT_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:19.449856+00:00
-- url     : https://prove2.me/submissions/149cf7b4-300f-4fd6-b6b6-c7262f99b09e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_eq
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_lift_comm_Aop
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_Aop_mul
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_mul
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
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ γ δ, κ τ (γ * δ) = κ τ γ * κ τ δ) (hρ : ∀ γ δ, ρ (γ * δ) = ρ γ * ρ δ)
    (γ δ : Γ) : actT lab κ ρ (γ * δ) = actT lab κ ρ γ * actT lab κ ρ δ := by
  simp only [actT_eq, hκ, hρ, Aop_mul, lift_mul, mul_assoc]
  congr 1
  rw [← mul_assoc, (lift_comm_Aop _ _).eq, mul_assoc]
end PositivityTheory.Rg.Cz.TGK
