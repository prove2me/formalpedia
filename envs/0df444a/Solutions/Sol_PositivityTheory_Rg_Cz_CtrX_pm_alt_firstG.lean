-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.pm_alt_firstG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:31:03.24511+00:00
-- url     : https://prove2.me/submissions/9db3e15b-45d7-4808-b8b7-0aafbde352b6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution {m k : ℕ} (τ : Equiv.Perm (Fin m)) (hτ : τ ∈ firstG m k) (x : TV n M (Fin m)) :
    pm τ (alt (firstG m k) x) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • alt (firstG m k) x := by
  have hmem : ∀ σ : Equiv.Perm (Fin m), σ ∈ firstG m k ↔ ∀ j : Fin m, k ≤ (j : ℕ) → σ j = j := by
    intro σ
    simp [firstG]
  have hτ' := (hmem τ).1 hτ
  have hmul : ∀ σ : Equiv.Perm (Fin m), pm τ (pm σ x) = pm (τ * σ) x := by
    intro σ
    funext I
    rfl
  simp only [alt, LinearMap.sum_apply, map_sum, Finset.smul_sum, LinearMap.smul_apply, map_smul, hmul, smul_smul]
  refine Finset.sum_nbij' (fun σ => τ * σ) (fun σ => τ⁻¹ * σ) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [hmem] at hσ ⊢
    intro j hj
    simp [Equiv.Perm.mul_apply, hσ j hj, hτ' j hj]
  · intro σ hσ
    rw [hmem] at hσ ⊢
    intro j hj
    have h1 : τ⁻¹ j = j := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (hτ' j hj).symm
    simp [Equiv.Perm.mul_apply, hσ j hj, h1]
  · intro σ _
    simp
  · intro σ _
    simp
  · intro σ _
    congr 1
    rw [Equiv.Perm.sign_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
end PositivityTheory.Rg.Cz.CtrX
