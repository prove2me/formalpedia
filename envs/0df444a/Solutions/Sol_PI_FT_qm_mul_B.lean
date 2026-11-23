-- Prove2me | solution 1 for PI.FT.qm_mul_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:39.642202+00:00
-- url     : https://prove2.me/submissions/ecc923e9-5657-433c-a0fe-d40eab86d4a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Theorems.Thm_PI_FT_rowJ_mul

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
theorem _root_.solution (hxB : ∀ j, hE σ J (x 0) (fun i => B i j) = 0) : qm σ J x b * B = 0 := by
  ext i k
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [qm, Matrix.smul_mul, Matrix.smul_apply, rowJ_mul, hxB, smul_zero, Matrix.zero_apply]
end PI.FT
