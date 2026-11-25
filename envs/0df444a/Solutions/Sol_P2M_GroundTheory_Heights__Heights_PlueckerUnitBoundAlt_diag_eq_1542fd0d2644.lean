-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_diag_eq_1542fd0d2644
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:18.447663+00:00
-- url     : https://prove2.me/submissions/7e961974-a164-42e5-bf41-c087b64b44cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPlueckerUnitBound

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
open Matrix Finset
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.PlueckerUnitBoundAlt
namespace GroundTheory.Heights₂.Heights.PlueckerUnitBoundAlt
theorem _root_.solution {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, ‖Z a b‖ = 1) (a : Fin j) :
    (1 + Z * Zᴴ : Matrix (Fin j) (Fin j) ℂ) a a = (((1 + m : ℝ)) : ℂ) := by
  have hb : ∀ b, Z a b * Zᴴ b a = 1 := by
    intro b
    rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      hZ a b]
    norm_num
  rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply]
  simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.PlueckerUnitBoundAlt
