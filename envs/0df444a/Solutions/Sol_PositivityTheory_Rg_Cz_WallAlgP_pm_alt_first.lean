-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.pm_alt_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:44:25.382855+00:00
-- url     : https://prove2.me/submissions/c79f1e4d-de79-4d2a-bf26-6a10ac463a0c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_mem_firstG
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_sgn_sq
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
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.WallAlgP
theorem _root_.solution {m k : ℕ} (τ : Equiv.Perm (Fin m)) (hτ : τ ∈ firstG m k) (ξ : TV n M (Fin m)) :
    pm τ (alt (firstG m k) ξ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • alt (firstG m k) ξ := by
  rw [mem_firstG] at hτ
  simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_equiv (Equiv.mulLeft τ) ?_ ?_
  · intro σ
    simp only [mem_firstG, Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Function.comp_apply]
    constructor
    · intro h j hj; rw [h j hj, hτ j hj]
    · intro h j hj
      apply τ.injective; rw [h j hj, hτ j hj]
  · intro σ _
    simp only [Equiv.coe_mulLeft, Equiv.Perm.sign_mul, smul_smul]
    rw [show pm τ (pm σ ξ) = pm (τ * σ) ξ from rfl, Units.val_mul, Int.cast_mul, ← mul_assoc, sgn_sq, one_mul]
end PositivityTheory.Rg.Cz.WallAlgP
