-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_smul_coeff_mem_5255ac3f8e81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:34.032903+00:00
-- url     : https://prove2.me/submissions/89579a13-1a70-47ae-bb95-95339899ff2f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_mem_succ_43982fb32ce9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_act_X_5d3e9f420ff7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_smul_eq_af68eef4f60e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
theorem _root_.solution (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w)
    (c : MvPolynomial (Fin q) ℤ) {p : (Polynomial Ω)} (hp : ∀ n, p.coeff n ∈ gradedSpan w d t n) :
    ∀ n, (c • p).coeff n ∈ gradedSpan w d t n := by
  induction c using MvPolynomial.induction_on generalizing p with
  | C a =>
    intro n
    rw [smul_eq w hA, act, MvPolynomial.eval₂Hom_C, eq_intCast, ← C_eq_intCast, coeff_C_mul,
      ← zsmul_eq_mul]
    exact zsmul_mem (hp n) a
  | add a b ha hb =>
    intro n
    rw [add_smul, coeff_add]
    exact add_mem (ha hp n) (hb hp n)
  | mul_X a j ha =>
    rw [mul_smul]
    apply ha
    intro n
    rw [smul_eq w hA, act_X]
    cases n with
    | zero => simp [mul_assoc]
    | succ k =>
      rw [mul_assoc, coeff_C_mul, coeff_X_mul, mul_comm]
      exact mul_mem_succ w d t j (hp k)
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
