-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.detD_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:08.458795+00:00
-- url     : https://prove2.me/submissions/3f0f0a60-0648-4bce-9ed3-331c51b20efe

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
theorem _root_.solution (L : PeriodPair) : detD L ≠ 0 := by
  intro h
  have h' : L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re = 0 := by rw [← detD_eq_re_mul_im_sub]; exact h
  have hi := LinearIndependent.pair_iff.mp L.indep
  have key : ∀ s t : ℝ, s * L.ω₁.re + t * L.ω₂.re = 0 → s * L.ω₁.im + t * L.ω₂.im = 0 →
      s = 0 ∧ t = 0 := by
    intro s t h1 h2
    apply hi
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re]
      linarith
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.zero_im]
      linarith
  obtain ⟨e1, e2⟩ := key L.ω₂.im (-L.ω₁.im) (by linear_combination h') (by ring)
  obtain ⟨f1, f2⟩ := key L.ω₂.re (-L.ω₁.re) (by ring)
    (by linear_combination (-L.ω₂.re) * e2 + (-L.ω₁.re) * e1)
  exact one_ne_zero (key 1 0 (by linear_combination (-1 : ℝ) * f2)
    (by linear_combination (-1 : ℝ) * e2)).1
end PI.UnitaryGroupMassFormula.UnimodLocStd
