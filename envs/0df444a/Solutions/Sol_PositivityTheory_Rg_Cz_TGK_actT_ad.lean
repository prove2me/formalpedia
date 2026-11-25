-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.actT_ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:49.439923+00:00
-- url     : https://prove2.me/submissions/048b8441-0db4-457d-b8ae-21c3720c439b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_actT_eq
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_lift_comm_Aop
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_lift_comm_mAt
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_eAt_eq
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_mAt_mul_Aop
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_Aop_mul_mAt
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_conj_single
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_tE_sum
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
theorem _root_.solution {ι Γ : Type} [DecidableEq ι] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M)
    (hu : ∀ τ γ, κ τ γ * (κ τ γ)ᴴ = 1)
    (had : ∀ γ τ a b, ρ γ * E τ a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E τ c d) * ρ γ)
    (γ : Γ) (τ : ι) (a b : Fin n) :
    actT lab κ ρ γ * tE (fib lab τ) (E τ) a b =
      (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • tE (fib lab τ) (E τ) c d) * actT lab κ ρ γ := by
  rw [actT_eq, tE_sum]
  unfold tE
  simp only [eAt_eq]
  rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [mul_assoc, ← (lift_comm_Aop _ _).eq, ← mul_assoc, ← lift_mul, had, lift_mul, mul_assoc]
  · refine Finset.sum_congr rfl fun p hp => ?_
    simp only [fib, Finset.mem_filter] at hp
    rw [mul_assoc, Aop_mul_mAt, ← mul_assoc (mAt _ _), ← (lift_comm_mAt _ _ _).eq, mul_assoc, mAt_mul_Aop]
    congr 2
    simp only [hp.2]
    rw [conj_single (κ τ γ) a b, mul_assoc, mul_eq_one_comm.mp (hu τ γ), mul_one]
end PositivityTheory.Rg.Cz.TGK
