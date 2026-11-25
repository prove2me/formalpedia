-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartGram_mixedDisc_const_112c4e1043f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:46:05.390481+00:00
-- url     : https://prove2.me/submissions/5de79c19-9038-4dc2-a49b-72675a58cad6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramPolar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_sum_neg_one_pow_card_pow_f7e1a9601f23

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Finset
open ReciprocityTheory.ChartRestriction.G.Geo (mixedDisc)
namespace GroundTheory.Heights₂.Heights
namespace ChartGram
theorem _root_.solution {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun _ => A) = A.det := by
  unfold mixedDisc
  have h : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ _k ∈ S, A).det =
      ((-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D) * A.det := by
    intro S
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Matrix.det_smul, Fintype.card_fin]
    ring
  simp_rw [h, ← Finset.sum_mul, ChartGram.sum_neg_one_pow_card_pow]
  have : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  field_simp
end ChartGram
end GroundTheory.Heights₂.Heights
