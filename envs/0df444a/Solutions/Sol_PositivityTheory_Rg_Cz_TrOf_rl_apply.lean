-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TrOf.rl_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:52.620153+00:00
-- url     : https://prove2.me/submissions/1487b955-e49a-4ef5-8f0d-de2fc0ee4505

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransOf

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
open PositivityTheory.Rg.Cz.TrOf
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
omit [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
namespace PositivityTheory.Rg.Cz.TrOf
theorem _root_.solution (e : P ≃ Q) (f : TV n M P) (J : Q → Fin n) : rl e f J = f (J ∘ e) := rfl
end PositivityTheory.Rg.Cz.TrOf
