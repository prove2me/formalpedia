-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.YoungTableau.alt_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:39.734511+00:00
-- url     : https://prove2.me/submissions/b1d5abcf-1a51-41f4-b34a-2c24fb28b354

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungA
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_mem_colG
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
open PositivityTheory.Rg.Cz.YoungTableau
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]
namespace PositivityTheory.Rg.Cz.YoungTableau
theorem _root_.solution (col : X → C) (ξ : TV n M X) (J : X → Fin n) (π : Equiv.Perm X) (hπ : π ∈ colG col) :
    alt (colG col) ξ (J ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • alt (colG col) ξ J := by
  have hπ' := (mem_colG col π).1 hπ
  rw [alt_apply, alt_apply, Finset.smul_sum]
  refine Finset.sum_nbij' (fun σ => π * σ) (fun τ => π⁻¹ * τ) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [mem_colG] at hσ ⊢
    intro p
    simp only [Equiv.Perm.mul_apply]
    rw [hπ', hσ]
  · intro τ hτ
    rw [mem_colG] at hτ ⊢
    intro p
    have h := hπ' (π⁻¹ (τ p))
    rw [Equiv.Perm.mul_apply, ← h]
    simp [hτ]
  · intro σ _
    simp
  · intro τ _
    simp
  · intro σ _
    simp only [Equiv.Perm.coe_mul, Function.comp_assoc, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, smul_smul]
    congr 1
    rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
end PositivityTheory.Rg.Cz.YoungTableau
