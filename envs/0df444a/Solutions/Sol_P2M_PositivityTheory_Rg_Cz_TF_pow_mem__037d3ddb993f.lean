-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Cz_TF_pow_mem__037d3ddb993f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:59.18782+00:00
-- url     : https://prove2.me/submissions/a531d62b-54c3-4516-98ec-d9de848edd79

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (Z : Submodule ℂ U)
    (hZ : ∀ z ∈ Z, T z ∈ Z) : ∀ k : ℕ, ∀ z ∈ Z, (T ^ k) z ∈ Z := by
  intro k
  induction k with
  | zero => intro z hz; simpa using hz
  | succ k ih => intro z hz; rw [pow_succ', Module.End.mul_apply]; exact hZ _ (ih z hz)
end PositivityTheory.Rg.Cz.TF
