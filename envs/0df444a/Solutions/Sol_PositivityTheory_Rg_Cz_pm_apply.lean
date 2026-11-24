-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.pm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:43.636587+00:00
-- url     : https://prove2.me/submissions/54aaa50b-9c61-4d2a-9fab-cecf48741925

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
theorem _root_.solution (σ : Equiv.Perm P) (f : TV n M P) (I : P → Fin n) : pm σ f I = f (I ∘ σ) := rfl
end PositivityTheory.Rg.Cz
