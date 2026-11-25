-- Prove2me | solution 1 for PI.FT.Lm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:57.287798+00:00
-- url     : https://prove2.me/submissions/7adfe248-4241-4975-ac49-bf2b9625c908

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff

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
namespace PI.FT
theorem _root_.solution {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
    {B : Matrix (Fin (M + 1)) (Fin M) E} (hJ' : J' = Formalism.UG.cT (σ : E →+* E) B * J * B)
    (hd : J'.det ≠ 0) : Lm σ J J' B * B = 1 := by
  have h : Lm σ J J' B * B = J'⁻¹ * J' := by
    rw [hJ']
    simp only [Lm, Matrix.mul_assoc]
  rw [h]
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd)
end PI.FT
