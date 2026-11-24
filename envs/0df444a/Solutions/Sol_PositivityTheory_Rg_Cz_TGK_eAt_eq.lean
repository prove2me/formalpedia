-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.eAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:49.628649+00:00
-- url     : https://prove2.me/submissions/cfa42d9e-f7db-4045-a3f7-dff38870ccef

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
import Theorems.Thm_PositivityTheory_Rg_Cz_eAt_apply
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
theorem _root_.solution (p : P) (a b : Fin n) :
    (eAt p a b : Module.End ℂ (TV n M P)) = mAt p (Matrix.single a b 1) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [eAt_apply, mAt_apply]
  simp only [Matrix.single_apply]
  rcases eq_or_ne (I p) a with h | h
  · simp [h]
  · simp [h, Ne.symm h]
end PositivityTheory.Rg.Cz.TGK
