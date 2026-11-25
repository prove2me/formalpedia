-- Prove2me | solution 1 for PI.EF.PK.rectInt_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:41.539401+00:00
-- url     : https://prove2.me/submissions/3a41810b-7ffd-4eed-ac35-bc76df52c12f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Theorems.Thm_PI_EF_PK_rectInt_eq_zero
import Theorems.Thm_PI_EF_PK_gl_differentiable
import Theorems.Thm_PI_EF_PK_side_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (l a b c d : ℝ) (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectInt (ker l) a b c d = 2 * π * I := by
  have hbot : ∀ x : ℝ, (x : ℂ) + c * I ≠ 0 := by
    intro x h
    have := congrArg Complex.im h
    simp at this <;> linarith
  have htop : ∀ x : ℝ, (x : ℂ) + d * I ≠ 0 := by
    intro x h
    have := congrArg Complex.im h
    simp at this <;> linarith
  have hright : ∀ y : ℝ, (b : ℂ) + y * I ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this <;> linarith
  have hleft : ∀ y : ℝ, (a : ℂ) + y * I ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this <;> linarith
  have ftc : ∀ (G : ℂ → ℂ) (γ : ℝ → ℂ) (v : ℂ) (p q : ℝ), (∀ t, HasDerivAt γ v t) → Continuous γ →
      (∀ t, γ t ≠ 0) → (∀ t ∈ Set.uIcc p q, HasDerivAt G (1 / γ t) (γ t)) →
      ∫ t in p..q, v * (1 / (γ t - 0)) = G (γ q) - G (γ p) := by
    intro G γ v p q hγd hγc hne hG
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => G (γ t))
    · intro t ht
      beta_reduce
      have := (hG t ht).comp t (hγd t)
      rw [sub_zero, mul_comm]
      exact this
    · apply Continuous.intervalIntegrable
      exact continuous_const.mul (continuous_const.div (hγc.sub continuous_const) (fun t => by simpa using hne t))
  have hdx : ∀ (w : ℂ) (t : ℝ), HasDerivAt (fun x : ℝ => (x : ℂ) + w) 1 t := fun w t => by
    simpa using ((hasDerivAt_id (t : ℂ)).add_const w).comp_ofReal
  have hdy : ∀ (w : ℂ) (t : ℝ), HasDerivAt (fun y : ℝ => w + (y : ℂ) * I) I t := fun w t => by
    simpa using (((hasDerivAt_id (t : ℂ)).mul_const I).const_add w).comp_ofReal
  have B1 : (∫ x in a..b, 1 / (((x : ℂ) + c * I) - 0)) = Complex.log (b + c * I) - Complex.log (a + c * I) := by
    have := ftc Complex.log (fun x : ℝ => (x : ℂ) + c * I) 1 a b (hdx _) (by fun_prop) hbot
      (fun t _ => by
        rw [one_div]
        exact Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hc.ne))))
    simp only [one_mul] at this
    exact this
  have B2 : (∫ x in a..b, 1 / (((x : ℂ) + d * I) - 0)) = Complex.log (b + d * I) - Complex.log (a + d * I) := by
    have := ftc Complex.log (fun x : ℝ => (x : ℂ) + d * I) 1 a b (hdx _) (by fun_prop) htop
      (fun t _ => by
        rw [one_div]
        exact Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hd.ne'))))
    simp only [one_mul] at this
    exact this
  have B3 : I * (∫ y in c..d, 1 / (((b : ℂ) + y * I) - 0)) = Complex.log (b + d * I) - Complex.log (b + c * I) := by
    rw [← intervalIntegral.integral_const_mul]
    exact ftc Complex.log (fun y : ℝ => (b : ℂ) + y * I) I c d (hdy _) (by fun_prop) hright
      (fun t _ => by
        rw [one_div]
        exact Complex.hasDerivAt_log (Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hb))))
  have B4 : I * (∫ y in c..d, 1 / (((a : ℂ) + y * I) - 0)) =
      Complex.log (-((a : ℂ) + d * I)) - Complex.log (-((a : ℂ) + c * I)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact ftc (fun z => Complex.log (-z)) (fun y : ℝ => (a : ℂ) + y * I) I c d (hdy _) (by fun_prop) hleft
      (fun t _ => by
        have hm : -((a : ℂ) + t * I) ∈ Complex.slitPlane :=
          Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using ha))
        convert (Complex.hasDerivAt_log hm).comp ((a : ℂ) + t * I) (hasDerivAt_neg ((a : ℂ) + t * I)) using 1
        all_goals (try rfl)
        all_goals (rw [one_div, inv_neg]; ring))
  have hz : ∀ z : ℂ, Complex.log z - Complex.log (-z) = ((Complex.arg z : ℂ) - (Complex.arg (-z) : ℂ)) * I := by
    intro z
    simp only [Complex.log, norm_neg]
    ring
  have e1 := hz ((a : ℂ) + d * I)
  have e2 := hz ((a : ℂ) + c * I)
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simpa using hd)] at e1
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hc)] at e2
  push_cast at e1 e2
  have hinv : (∫ x in a..b, 1 / (((x : ℂ) + c * I) - 0)) - (∫ x in a..b, 1 / (((x : ℂ) + d * I) - 0))
      + I * (∫ y in c..d, 1 / (((b : ℂ) + y * I) - 0)) - I * (∫ y in c..d, 1 / (((a : ℂ) + y * I) - 0))
      = 2 * π * I := by
    rw [B1, B2, B3, B4]
    linear_combination e1 - e2
  have s1 := side_split l (fun x : ℝ => (x : ℂ) + c * I) (by fun_prop) hbot a b
  have s2 := side_split l (fun x : ℝ => (x : ℂ) + d * I) (by fun_prop) htop a b
  have s3 := side_split l (fun y : ℝ => (b : ℂ) + y * I) (by fun_prop) hright c d
  have s4 := side_split l (fun y : ℝ => (a : ℂ) + y * I) (by fun_prop) hleft c d
  beta_reduce at s1 s2 s3 s4
  have hg := rectInt_eq_zero (gl l) a b c d (gl_differentiable l).differentiableOn
  unfold rectInt at hg ⊢
  simp only [smul_eq_mul] at hg ⊢
  rw [s1, s2, s3, s4]
  linear_combination hg + hinv
end PI.EF.PK
