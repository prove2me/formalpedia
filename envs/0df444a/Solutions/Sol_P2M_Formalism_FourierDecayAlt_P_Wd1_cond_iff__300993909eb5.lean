-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Wd1_cond_iff__300993909eb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:05.693889+00:00
-- url     : https://prove2.me/submissions/d9e7cffd-9801-4ce4-9ab3-d540e902122c

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd1
open Matrix Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd1
theorem _root_.solution (a : S) (i j : Fin 2) (x y : Ix S) :
    (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (y a = j ∧ x = Function.update y a i) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, ?_⟩
    funext b
    by_cases hb : b = a
    · subst hb; simp [h1]
    · simp [Function.update_apply, hb, h3 b hb]
  · rintro ⟨h2, rfl⟩
    exact ⟨by simp, h2, fun b hb => by simp [Function.update_apply, hb]⟩
end Formalism.FourierDecayAlt.P.Wd1
