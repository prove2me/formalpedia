-- Prove2me | solution 1 for PI.HookSteps.Cap.alt_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:19.720649+00:00
-- url     : https://prove2.me/submissions/7b387ca6-8f51-4f6d-859b-8906baeb1256

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open Finset
variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]
namespace PI.HookSteps.Cap
theorem _root_.solution {k : ℕ} (F : I → 𝒰) (Δ : (Fin k → I) → 𝒰) (r : Fin (k + 1) → I)
    (hIH : ∀ r' : Fin k → I,
      ∑ τ : Equiv.Perm (Fin k), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • Δ (fun j => r' (τ j)) = 0) :
    ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      (F (r (σ 0)) * Δ (fun i => r (σ i.succ))) = 0 := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun p _ => ?_
  simp only [Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  have h0 : ∑ τ : Equiv.Perm (Fin k), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) •
      Δ (fun i => r (Equiv.swap 0 p (τ i).succ)) = 0 := hIH (fun j => r (Equiv.swap 0 p j.succ))
  calc _ = F (r p) * (((if p = 0 then 1 else -1 : ℤˣ) : ℤ) • ∑ τ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • Δ (fun i => r (Equiv.swap 0 p (τ i).succ))) := by
        rw [Finset.smul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Units.val_mul, mul_smul, mul_smul_comm, mul_smul_comm]
    _ = 0 := by rw [h0, smul_zero, mul_zero]
end PI.HookSteps.Cap
