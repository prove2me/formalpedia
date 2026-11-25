-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.lift_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:30.435002+00:00
-- url     : https://prove2.me/submissions/c3bb6c83-e08a-48f6-a0ad-b7a526e427f2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFin
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
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} (c : ℂ) :
    (lift (algebraMap ℂ (Module.End ℂ M) c) : Module.End ℂ (TV n M P)) = algebraMap ℂ _ c := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp [lift, Algebra.algebraMap_eq_smul_one]
end PositivityTheory.Rg.Cz.TF
