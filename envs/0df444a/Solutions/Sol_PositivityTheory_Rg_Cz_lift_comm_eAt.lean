-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.lift_comm_eAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:38.837575+00:00
-- url     : https://prove2.me/submissions/3889d02e-c9fe-45b5-a42b-dfc1b2a249b4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_eAt_apply
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
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (B : Module.End ℂ M) (p : P) (a b : Fin n) : Commute (lift B) (eAt p a b) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, lift_apply, eAt_apply]
  split_ifs <;> simp
end PositivityTheory.Rg.Cz
