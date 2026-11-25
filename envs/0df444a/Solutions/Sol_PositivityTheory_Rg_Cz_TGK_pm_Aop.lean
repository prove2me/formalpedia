-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.pm_Aop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:14.093326+00:00
-- url     : https://prove2.me/submissions/994ff078-344e-497e-ae73-c4cda0ed7369

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_Aop_apply
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
theorem _root_.solution (σ : Equiv.Perm P) (K : P → Matrix (Fin n) (Fin n) ℂ) (hK : ∀ q, K (σ q) = K q) :
    (pm σ * Aop K : Module.End ℂ (TV n M P)) = Aop K * pm σ := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, pm_apply, Aop_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin n)) : (P → Fin n) ≃ (P → Fin n)) _ _ fun J => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_def, id, Equiv.symm_apply_apply]
  congr 1
  conv_rhs => rw [← Equiv.prod_comp σ]
  simp [hK]
end PositivityTheory.Rg.Cz.TGK
