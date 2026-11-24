-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.spl_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:27.123784+00:00
-- url     : https://prove2.me/submissions/93276df7-3a42-4484-ab96-331010201139

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB

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
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]
omit [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution (F : TV n M P) (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) :
    spl q F J I = F (merge q J I) := rfl
end PositivityTheory.Rg.Cz.TA
