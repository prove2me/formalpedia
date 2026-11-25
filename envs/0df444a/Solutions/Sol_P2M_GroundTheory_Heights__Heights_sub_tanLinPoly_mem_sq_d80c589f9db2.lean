-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sub_tanLinPoly_mem_sq_d80c589f9db2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:14.929486+00:00
-- url     : https://prove2.me/submissions/07ae2792-4825-43d1-8998-efa26ec14099

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_polyDiff_apply_f452501de9f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tanLinPoly_add_3cf296cf920c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tanLinPoly_smul_6210bcafaeca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tanLinPoly_zero_a4dc94d63023
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tanLinPoly_single_f8c00c20ae32
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_sub_C_mem_ker_2ebe1b0d4571

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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) - tanLinPoly p (polyDiff p f) ∈ RingHom.ker (eval p) ^ 2 := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : polyDiff p (C a) = 0 := by ext j; simp [polyDiff_apply]
    simp [h, tanLinPoly_zero]
  | add f g hf hg =>
    have e : f + g - C (eval p (f + g)) - tanLinPoly p (polyDiff p (f + g)) =
        (f - C (eval p f) - tanLinPoly p (polyDiff p f)) +
          (g - C (eval p g) - tanLinPoly p (polyDiff p g)) := by
      rw [map_add, map_add, map_add, tanLinPoly_add]; ring
    rw [e]
    exact add_mem hf hg
  | mul_X f i hf =>
    have hd : polyDiff p (f * X i) = p i • polyDiff p f + eval p f • Pi.single i 1 := by
      ext j
      simp only [polyDiff_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Derivation.leibniz,
        pderiv_X, map_add]
      by_cases hij : i = j
      · subst hij
        simp only [Pi.single_eq_same, mul_one, map_mul, eval_X]
        ring
      · simp only [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), mul_zero, map_zero,
          map_mul, eval_X, zero_add, add_zero]
    have e : f * X i - C (eval p (f * X i)) - tanLinPoly p (polyDiff p (f * X i)) =
        C (p i) * (f - C (eval p f) - tanLinPoly p (polyDiff p f)) +
          (f - C (eval p f)) * (X i - C (p i)) := by
      rw [hd, tanLinPoly_add, tanLinPoly_smul, tanLinPoly_smul, tanLinPoly_single, map_mul, eval_X, map_mul]
      ring
    rw [e]
    refine add_mem (Ideal.mul_mem_left _ _ hf) ?_
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (X_sub_C_mem_ker p i)
    simp [RingHom.mem_ker]
end GroundTheory.Heights₂.Heights
