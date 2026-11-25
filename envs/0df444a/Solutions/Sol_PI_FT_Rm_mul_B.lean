-- Prove2me | solution 1 for PI.FT.Rm_mul_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:59.761414+00:00
-- url     : https://prove2.me/submissions/0cd04406-62c5-4159-9543-30fbfedebb01

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Theorems.Thm_PI_FT_qm_mul_B

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
theorem _root_.solution (hLB : Lm σ J J' B * B = 1) (hxB : ∀ j, hE σ J (x 0) (fun i => B i j) = 0) :
    Rm σ J J' B x b * B = 1 := by
  rw [Rm, Matrix.sub_mul, Matrix.mul_assoc (Lm σ J J' B * Xc x), qm_mul_B σ hxB, Matrix.mul_zero,
    sub_zero, hLB]
end PI.FT
