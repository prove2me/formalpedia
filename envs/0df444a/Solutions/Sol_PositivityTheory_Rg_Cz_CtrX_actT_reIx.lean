-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.actT_reIx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:03.071471+00:00
-- url     : https://prove2.me/submissions/81100ee0-bbea-4979-960f-a07c66bdb0a9

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
theorem _root_.solution {ι Γ P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] (e : P ≃ Q)
    (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) (ξ : TV n M P) :
    actT (lab ∘ e.symm) κ ρ γ (reIx e ξ) = reIx e (actT lab κ ρ γ ξ) := by
  funext I
  simp only [actT, reIx, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply]
  symm
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl (Fin n))) _ _ (fun J => ?_)
  have hJ : (e.arrowCongr (Equiv.refl (Fin n)) J) ∘ e = J := by
    funext p
    simp [Equiv.arrowCongr_apply]
  rw [hJ]
  congr 1
  refine Fintype.prod_equiv e _ _ (fun p => ?_)
  simp [Equiv.arrowCongr_apply]
end PositivityTheory.Rg.Cz.CtrX
