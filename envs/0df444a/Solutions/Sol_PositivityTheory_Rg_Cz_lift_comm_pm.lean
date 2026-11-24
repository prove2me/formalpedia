-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.lift_comm_pm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:52.116029+00:00
-- url     : https://prove2.me/submissions/a785bda0-7cb3-472e-9f7e-1795065013e5

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
theorem _root_.solution (B : Module.End ℂ M) (σ : Equiv.Perm P) : Commute (lift B : Module.End ℂ (TV n M P)) (pm σ) := rfl
end PositivityTheory.Rg.Cz
