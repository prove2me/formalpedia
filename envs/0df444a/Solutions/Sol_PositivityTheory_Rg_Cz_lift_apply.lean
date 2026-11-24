-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.lift_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:43.35675+00:00
-- url     : https://prove2.me/submissions/fd73e7c8-16f1-4206-81e1-3c633859b748

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (B : Module.End ℂ M) (f : TV n M P) (I : P → Fin n) : lift B f I = B (f I) := rfl
end PositivityTheory.Rg.Cz
