-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LineChowForm_aeval_substZeroOneOne_8aa7d728ad3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:14.299517+00:00
-- url     : https://prove2.me/submissions/a92c9307-4106-470c-8e28-5ae5cda8eb09

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LineChowForm
variable {F : Type*} [Field F]
variable {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.LineChowForm
theorem _root_.solution {A : Type*} [CommRing A] [Algebra F A] (w : Fin 2 × Fin 2 → A)
    (r : MvPolynomial (Fin 2 × Fin 2) F) :
    aeval w (substZeroOneOne r) = aeval (Function.update w (1,1) 0) r := by
  have : ((aeval w).comp substZeroOneOne : MvPolynomial (Fin 2 × Fin 2) F →ₐ[F] A) =
      aeval (Function.update w (1,1) 0) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i = (1,1)
    · subst hi; simp [substZeroOneOne]
    · simp [substZeroOneOne, hi, Function.update_of_ne hi]
  exact DFunLike.congr_fun this r
end GroundTheory.Heights₂.Heights.LineChowForm
