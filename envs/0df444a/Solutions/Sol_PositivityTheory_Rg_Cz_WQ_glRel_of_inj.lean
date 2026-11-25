-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WQ.glRel_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:32.150076+00:00
-- url     : https://prove2.me/submissions/90001776-73ff-49b5-982a-7df8fd96a3ba

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.WQ
variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
namespace PositivityTheory.Rg.Cz.WQ
theorem _root_.solution (f : A →ₐ[ℂ] B) (hf : Function.Injective f) {n : ℕ} {E : Fin n → Fin n → A}
    (h : GlRel fun a b => f (E a b)) : GlRel E := by
  intro a b c d
  apply hf
  simpa [map_sub, map_mul, apply_ite f] using h a b c d
end PositivityTheory.Rg.Cz.WQ
