-- Prove2me | solution 1 for PI.FT.Rm_mul_Xc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:02.801103+00:00
-- url     : https://prove2.me/submissions/7683b274-c403-4702-bec8-8820ada8b3e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Theorems.Thm_PI_FT_qm_mul_Xc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
variable {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
  {B : Matrix (Fin (M + 1)) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {b : E}
namespace PI.FT
theorem _root_.solution (hb : b ≠ 0) (hx : hE σ J (x 0) (x 0) = b) : Rm σ J J' B x b * Xc x = 0 := by
  rw [Rm, Matrix.sub_mul, Matrix.mul_assoc (Lm σ J J' B * Xc x), qm_mul_Xc σ hb hx, Matrix.mul_one,
    sub_self]
end PI.FT
