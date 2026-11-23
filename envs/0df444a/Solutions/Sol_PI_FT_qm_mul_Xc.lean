-- Prove2me | solution 1 for PI.FT.qm_mul_Xc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:39.714412+00:00
-- url     : https://prove2.me/submissions/535bac0e-7e17-4ded-bf21-ea9d2e9fe412

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
theorem _root_.solution (hb : b ≠ 0) (hx : hE σ J (x 0) (x 0) = b) : qm σ J x b * Xc x = 1 := by
  have hc : (fun i => Xc x i 0) = x 0 := rfl
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [qm, Matrix.smul_mul, Matrix.smul_apply, rowJ_mul, hc, hx, Matrix.one_apply_eq, smul_eq_mul,
    inv_mul_cancel₀ hb]
end PI.FT
