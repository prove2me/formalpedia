-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.cj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:30.797329+00:00
-- url     : https://prove2.me/submissions/c08fc724-3635-4793-b72a-cbeef07756a8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W)
    (X : Module.End ℂ W) (v : V) : cj e X v = e.symm (X (e v)) := rfl
end PositivityTheory.Rg.Cz.TA
