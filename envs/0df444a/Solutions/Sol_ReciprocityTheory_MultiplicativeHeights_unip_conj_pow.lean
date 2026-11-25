-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_conj_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:36:54.733556+00:00
-- url     : https://prove2.me/submissions/f2fad8cd-2eff-4bf0-9816-caaf58af53a4

import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentA
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) (n : ℕ) :
    (Q * M * Q⁻¹) ^ n = Q * M ^ n * Q⁻¹ := by
  have hinv : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ)
  have hinv' : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  induction n with
  | zero => simp [hinv']
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc Q * M ^ n * Q⁻¹ * (Q * M * Q⁻¹) = Q * M ^ n * (Q⁻¹ * Q) * M * Q⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = Q * (M ^ n * M) * Q⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
end ReciprocityTheory.MultiplicativeHeights
