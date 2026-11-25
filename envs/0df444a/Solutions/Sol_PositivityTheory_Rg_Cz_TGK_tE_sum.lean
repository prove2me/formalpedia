-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.tE_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:19.631149+00:00
-- url     : https://prove2.me/submissions/6e778cd4-b231-49f6-8511-5febaa767c86

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Theorems.Thm_PositivityTheory_Rg_Cz_TGK_eAt_eq
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
theorem _root_.solution (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (k : Fin n → Fin n → ℂ) :
    ∑ c, ∑ d, k c d • tE S E c d =
      lift (∑ c, ∑ d, k c d • E c d) + ∑ p ∈ S, mAt p (∑ c, ∑ d, k c d • Matrix.single c d (1 : ℂ)) := by
  simp only [tE, smul_add, Finset.sum_add_distrib, Finset.smul_sum, eAt_eq]
  congr 1
  · refine LinearMap.ext fun f => funext fun I => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply]
  · have : ∀ p, (mAt p (∑ c, ∑ d, k c d • Matrix.single c d (1 : ℂ)) : Module.End ℂ (TV n M P)) =
        ∑ c, ∑ d, k c d • mAt p (Matrix.single c d 1) := fun p => by
      rw [show (mAt p : _ → Module.End ℂ (TV n M P)) = mAtL p from rfl]
      simp only [map_sum, map_smul]
    simp only [this]
    conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
end PositivityTheory.Rg.Cz.TGK
