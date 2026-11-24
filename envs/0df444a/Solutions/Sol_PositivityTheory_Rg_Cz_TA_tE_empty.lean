-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.tE_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:31.159809+00:00
-- url     : https://prove2.me/submissions/a293e362-5fa4-4a34-90e1-ab0f14467be5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution (F : Fin n → Fin n → Module.End ℂ M) :
    (tE (∅ : Finset P) F : Fin n → Fin n → Module.End ℂ (TV n M P)) = fun a b => lift (F a b) := by
  funext a b
  simp [tE]
end PositivityTheory.Rg.Cz.TA
