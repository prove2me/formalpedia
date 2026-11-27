-- Prove2me | solution 1 for PI.QnRT.ruleTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:20:46.585909+00:00
-- url     : https://prove2.me/submissions/92ce0bec-27f8-44bd-8dfa-20d87696e53f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
import Theorems.Thm_PI_QnRT_X1_eq
import Theorems.Thm_PI_QnRT_depthNumbers_threshold_eq
import Theorems.Thm_PI_QnRT_first_hermitian_part_diagonal
import Theorems.Thm_PI_QnRT_second_hermitian_part_diagonal
import Theorems.Thm_P2M_PI_QnRT_rdV_dz__4662447fe890
import Theorems.Thm_PI_QnRT_lin_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution : RuleTorus := by
  intro E _ _ k r l D f hD hf c hcO g₁ hg₁ hcD
  have hc : c l ≠ 0 := hcO l
  constructor
  · show RdV _ f _ + Complex.I • RdV _ f _ = _
    rw [X1_eq, depthNumbers_threshold_eq, rdV_dz' l D f hf c hc g₁ hg₁ hcD ((1 / 2 : ℝ) : ℂ) (-((1 / 2 : ℝ) : ℂ)) (by simp),
      rdV_dz' l D f hf c hc g₁ hg₁ hcD (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I)
        (by simp)]
    unfold pOp wirt
    rw [if_pos hcO]
    generalize fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c = L'
    rw [lin_single l L' (c l * ((1 / 2 : ℝ) : ℂ)),
      lin_single l L' (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize hA : L' (Pi.single l (1 : ℂ)) = A
    generalize hB : L' (Pi.single l Complex.I) = B
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    conv_rhs => rw [← Complex.re_add_im (c l)]
    try simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    generalize (c l).re = a
    generalize (c l).im = b
    match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf
  · show RdV _ f _ + Complex.I • RdV _ f _ = _
    rw [first_hermitian_part_diagonal, second_hermitian_part_diagonal, rdV_dz' l D f hf c hc g₁ hg₁ hcD (-((1 / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) (by simp),
      rdV_dz' l D f hf c hc g₁ hg₁ hcD (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I)
        (by simp)]
    unfold pbOp wirtBar
    rw [if_pos hcO]
    generalize fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c = L'
    rw [lin_single l L' (c l * -((1 / 2 : ℝ) : ℂ)),
      lin_single l L' (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize hA : L' (Pi.single l (1 : ℂ)) = A
    generalize hB : L' (Pi.single l Complex.I) = B
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    conv_rhs => rw [← Complex.re_add_im (c l)]
    try simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    generalize (c l).re = a
    generalize (c l).im = b
    match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf
end PI.QnRT
