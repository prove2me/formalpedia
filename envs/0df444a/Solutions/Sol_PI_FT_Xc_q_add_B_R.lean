-- Prove2me | solution 1 for PI.FT.Xc_q_add_B_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:46:09.180801+00:00
-- url     : https://prove2.me/submissions/8751f1ee-ef14-47aa-9291-34d96f4f3cf0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Theorems.Thm_PI_FT_qm_mul_Xc
import Theorems.Thm_PI_FT_qm_mul_B
import Theorems.Thm_PI_FT_Rm_mul_Xc
import Theorems.Thm_PI_FT_Rm_mul_B

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
theorem _root_.solution (hb : b ≠ 0) (hx : hE σ J (x 0) (x 0) = b)
    (hxB : ∀ j, hE σ J (x 0) (fun i => B i j) = 0) (hLB : Lm σ J J' B * B = 1) :
    Xc x * qm σ J x b + B * Rm σ J J' B x b = 1 := by
  have h1 : Matrix.fromRows (qm σ J x b) (Rm σ J J' B x b) * Matrix.fromCols (Xc x) B = 1 := by
    rw [Matrix.fromRows_mul_fromCols, qm_mul_Xc σ hb hx, qm_mul_B σ hxB, Rm_mul_Xc σ hb hx,
      Rm_mul_B σ hLB hxB, Matrix.fromBlocks_one]
  have e : Fin 1 ⊕ Fin M ≃ Fin (M + 1) :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  have h2 := (Matrix.mul_eq_one_comm_of_equiv e).mp h1
  rwa [Matrix.fromCols_mul_fromRows] at h2
end PI.FT
