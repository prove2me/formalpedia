-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WQ.glRel_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:39:06.362573+00:00
-- url     : https://prove2.me/submissions/a4d027eb-5668-4267-99d9-5eea48aa5330

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
theorem _root_.solution (f : A →ₐ[ℂ] B) {n : ℕ} {E : Fin n → Fin n → A} (h : GlRel E) : GlRel fun a b => f (E a b) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simpa [map_sub, map_mul, apply_ite f] using this
end PositivityTheory.Rg.Cz.WQ
