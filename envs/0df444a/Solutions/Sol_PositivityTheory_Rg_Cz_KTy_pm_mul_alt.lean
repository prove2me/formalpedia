-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.KTy.pm_mul_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:35:58.640516+00:00
-- url     : https://prove2.me/submissions/ab39e5bd-c33b-4a4c-bf68-5d471fd51e7d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_mul
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
open PositivityTheory.Rg.Cz.KTy
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace PositivityTheory.Rg.Cz.KTy
theorem _root_.solution {P : Type} [Fintype P] [DecidableEq P] {M : Type} [AddCommGroup M] [Module ℂ M]
    (G : Finset (Equiv.Perm P)) (σ₀ : Equiv.Perm P) (h : ∀ σ, σ₀ * σ ∈ G ↔ σ ∈ G) :
    (pm σ₀ * alt G : Module.End ℂ (TV n M P)) = ((Equiv.Perm.sign σ₀ : ℤ) : ℂ) • alt G := by
  unfold alt
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_nbij' (fun σ => σ₀ * σ) (fun σ => σ₀⁻¹ * σ) (fun σ hσ => (h σ).2 hσ)
    (fun σ hσ => (h _).1 (by simpa using hσ)) (fun σ _ => by simp) (fun σ _ => by simp) (fun σ _ => ?_)
  have e : ((Equiv.Perm.sign σ₀ : ℤ) : ℂ) * ((Equiv.Perm.sign σ₀ : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  rw [mul_smul_comm, ← pm_mul, smul_smul]
  congr 1
  rw [Equiv.Perm.sign_mul]
  push_cast
  linear_combination -(((Equiv.Perm.sign σ : ℤ) : ℂ)) * e
end PositivityTheory.Rg.Cz.KTy
