-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Wd7_cond_iff__d5515724d8c4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:07.239569+00:00
-- url     : https://prove2.me/submissions/847635ac-01b9-4fd0-a3bd-ee5878e14b42

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (a : S) (i j : Fin 2) (x y : Ix S) :
    (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (y a = j ∧ x = Function.update y a i) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, ?_⟩
    funext b
    by_cases hb : b = a
    · subst hb; simp [h1]
    · simp [Function.update_of_ne hb, h3 b hb]
  · rintro ⟨h1, rfl⟩
    refine ⟨by simp, h1, ?_⟩
    intro b hb
    simp [Function.update_of_ne hb]
end Formalism.FourierDecayAlt.P.Wd7
