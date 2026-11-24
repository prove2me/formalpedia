-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.eAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:30.571719+00:00
-- url     : https://prove2.me/submissions/231adc67-4c5d-4950-86f1-4be73dbb0cd9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply

set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (p : P) (a b : Fin n) (f : TV n M P) (I : P → Fin n) :
    eAt p a b f I = if I p = a then f (Function.update I p b) else 0 := by
  simp only [eAt, LinearMap.pi_apply]
  split_ifs <;> simp
end PositivityTheory.Rg.Cz
