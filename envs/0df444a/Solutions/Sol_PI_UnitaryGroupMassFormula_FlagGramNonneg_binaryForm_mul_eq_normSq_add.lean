-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.binaryForm_mul_eq_normSq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:46.008354+00:00
-- url     : https://prove2.me/submissions/8a1d2da9-07f1-478c-8714-b4f0028e9ac3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_BinaryFormMulEqNormSqAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution (T T' : ℝ) (s x y : ℂ) :
    T * (T * Complex.normSq x + T' * Complex.normSq y - 2 * (conj x * s * y).re) =
      Complex.normSq ((T : ℂ) * x - s * y) + (T * T' - Complex.normSq s) * Complex.normSq y := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring
end PI.UnitaryGroupMassFormula.FlagGramNonneg
