-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.im_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:35.192618+00:00
-- url     : https://prove2.me/submissions/aa7387df-561b-4f82-9502-799805158fde

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply


section
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
private theorem detD_eq_re_mul_im_sub (L : PeriodPair) :
    detD L = L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re := by
  simp only [detD, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (L : PeriodPair) (p q r s : ℝ) :
    ((p • L.ω₁ + q • L.ω₂) * conj (r • L.ω₁ + s • L.ω₂)).im = (q * r - p * s) * detD L := by
  rw [detD_eq_re_mul_im_sub]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, Complex.conj_re, Complex.conj_im, smul_eq_mul]
  ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
