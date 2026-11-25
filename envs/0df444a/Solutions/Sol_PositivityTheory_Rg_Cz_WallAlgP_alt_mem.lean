-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.alt_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:27.897841+00:00
-- url     : https://prove2.me/submissions/b2d519f1-b4ef-45c5-bd28-f07627e97a42

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
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
theorem _root_.solution {m k : ℕ} (X : Submodule ℂ (TV n M (Fin m))) (hP : ∀ σ, ∀ ξ ∈ X, pm σ ξ ∈ X) (ξ) (hξ : ξ ∈ X) :
    alt (firstG m k) ξ ∈ X := by
  rw [alt, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  exact X.sum_mem fun σ _ => X.smul_mem _ (hP σ ξ hξ)
end PositivityTheory.Rg.Cz.WallAlgP
