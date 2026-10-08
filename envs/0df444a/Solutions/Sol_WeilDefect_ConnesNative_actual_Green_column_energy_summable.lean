-- Prove2me | solution 1 for WeilDefect.ConnesNative.actual_Green_column_energy_summable
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T03:30:25.273981+00:00
-- url     : https://prove2.me/submissions/9e106c07-da47-4395-b268-692144339078

import Definitions.Def_ConnesGreen_canonical_model
import Theorems.Thm_ConnesRZ_actual_zero_reciprocal_square_summable
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory Set ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp ENNReal Classical Topology Interval ComplexConjugate
noncomputable section
namespace WeilDefect
attribute [local instance 1100] NormedSpace.complexToReal
open Filter Set Bornology
theorem hasDerivAt_realExpMode (freq : ℂ) (x : ℝ) :
    HasDerivAt (realExpMode freq) (freq * realExpMode freq x) x := by
  have hcomplex :
      HasDerivAt
        (fun z : ℂ => Complex.exp (z * freq))
        (freq * Complex.exp ((x : ℂ) * freq))
        (x : ℂ) := by
    have h :=
      hasDerivAt_exp_smul_const' (𝕂 := ℂ) (𝔸 := ℂ) freq (x : ℂ)
    simpa [← Complex.exp_eq_exp_ℂ, smul_eq_mul] using h
  change HasDerivAt
    (fun y : ℝ => Complex.exp ((y : ℂ) * freq))
    (freq * Complex.exp ((x : ℂ) * freq))
    x
  exact hcomplex.comp_ofReal

theorem iteratedDeriv_realExpMode (k : ℕ) (freq : ℂ) :
    iteratedDeriv k (realExpMode freq) =
      fun x : ℝ => freq ^ k * realExpMode freq x := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have h :=
        (hasDerivAt_realExpMode freq x).const_mul (freq ^ k)
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h.deriv

theorem contDiffAt_const_mul_realExpMode
    (k : ℕ) (c freq : ℂ) (x : ℝ) :
    ContDiffAt ℝ k (fun y : ℝ => c * realExpMode freq y) x := by
  change ContDiffAt ℝ k (fun y => c * Complex.exp (Complex.ofRealCLM y * freq)) x
  fun_prop

noncomputable def problemOneDenominator (freq : ℂ) : ℂ :=
  (1 / 4 : ℂ) - freq ^ 2

theorem problemOneL_realExpMode (freq : ℂ) (x : ℝ) :
    problemOneL (realExpMode freq) x =
      problemOneDenominator freq * realExpMode freq x := by
  simp [problemOneL, problemOneDenominator, iteratedDeriv_realExpMode]
  ring

theorem problemOneL_const_mul
    (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    problemOneL (fun y => c * f y) x =
      c * problemOneL f x := by
  simp [problemOneL, iteratedDeriv_const_mul_field]
  ring

theorem problemOneL_const_mul_realExpMode
    (c freq : ℂ) (x : ℝ) :
    problemOneL (fun y => c * realExpMode freq y) x =
      c * problemOneDenominator freq * realExpMode freq x := by
  rw [problemOneL_const_mul, problemOneL_realExpMode]
  ring

theorem problemOneL_add
    (f g : ℝ → ℂ) (x : ℝ)
    (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    problemOneL (f + g) x =
      problemOneL f x + problemOneL g x := by
  simp [problemOneL, iteratedDeriv_add hf hg]
  ring

theorem problemOneDenominator_problemOneFreq (gamma : ℂ) :
    problemOneDenominator (problemOneFreq gamma) =
      problemOneGreenDenom gamma := by
  simp [problemOneDenominator, problemOneFreq, problemOneGreenDenom, mul_pow, Complex.I_sq]

theorem dirichletRightReal_neg (t : ℝ) :
    dirichletRightReal t (-t) = 0 := by
  simp [dirichletRightReal]

theorem dirichletLeftReal_pos (t : ℝ) :
    dirichletLeftReal t t = 0 := by
  simp [dirichletLeftReal]

theorem dirichletRightReal_pos
    (t : ℝ) (ht : t ≠ 0) :
    dirichletRightReal t t = 1 := by
  have hs : Real.sinh t ≠ 0 := Real.sinh_ne_zero.mpr ht
  simp [dirichletRightReal, hs]

theorem dirichletLeftReal_neg
    (t : ℝ) (ht : t ≠ 0) :
    dirichletLeftReal t (-t) = 1 := by
  have hs : Real.sinh t ≠ 0 := Real.sinh_ne_zero.mpr ht
  simp [dirichletLeftReal, hs]

theorem dirichletRightBasis_neg (t : ℝ) :
    dirichletRightBasis t (-t) = 0 := by
  simp [dirichletRightBasis, dirichletRightReal_neg]

theorem dirichletLeftBasis_pos (t : ℝ) :
    dirichletLeftBasis t t = 0 := by
  simp [dirichletLeftBasis, dirichletLeftReal_pos]

theorem dirichletRightBasis_pos
    (t : ℝ) (ht : t ≠ 0) :
    dirichletRightBasis t t = 1 := by
  simp [dirichletRightBasis, dirichletRightReal_pos t ht]

theorem dirichletLeftBasis_neg
    (t : ℝ) (ht : t ≠ 0) :
    dirichletLeftBasis t (-t) = 1 := by
  simp [dirichletLeftBasis, dirichletLeftReal_neg t ht]

theorem hasDerivAt_dirichletRightReal
    (t x : ℝ) :
    HasDerivAt
      (dirichletRightReal t)
      (Real.cosh ((t + x) / 2) / (2 * Real.sinh t))
      x := by
  have hinner : HasDerivAt (fun y : ℝ => (t + y) / 2) (1 / 2 : ℝ) x := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      ((hasDerivAt_const x t).add (hasDerivAt_id x)).div_const 2
  have h := hinner.sinh.div_const (Real.sinh t)
  have he : Real.cosh ((t + x) / 2) * (1 / 2) / Real.sinh t =
      Real.cosh ((t + x) / 2) / (2 * Real.sinh t) := by ring
  rw [he] at h
  exact h

theorem hasDerivAt_dirichletRightReal_deriv
    (t x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        Real.cosh ((t + y) / 2) / (2 * Real.sinh t))
      ((1 / 4 : ℝ) * dirichletRightReal t x)
      x := by
  have hinner : HasDerivAt (fun y : ℝ => (t + y) / 2) (1 / 2 : ℝ) x := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      ((hasDerivAt_const x t).add (hasDerivAt_id x)).div_const 2
  have h := hinner.cosh.div_const (2 * Real.sinh t)
  have he : (Real.sinh ((t + x) / 2) * (1 / 2)) / (2 * Real.sinh t) =
      (1 / 4 : ℝ) * dirichletRightReal t x := by
    unfold dirichletRightReal
    ring
  rw [he] at h
  exact h

theorem hasDerivAt_dirichletLeftReal
    (t x : ℝ) :
    HasDerivAt
      (dirichletLeftReal t)
      (-Real.cosh ((t - x) / 2) / (2 * Real.sinh t))
      x := by
  have hinner : HasDerivAt (fun y : ℝ => (t - y) / 2) (-1 / 2 : ℝ) x := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      ((hasDerivAt_const x t).sub (hasDerivAt_id x)).div_const 2
  have h := hinner.sinh.div_const (Real.sinh t)
  have he : Real.cosh ((t - x) / 2) * (-1 / 2) / Real.sinh t =
      -Real.cosh ((t - x) / 2) / (2 * Real.sinh t) := by ring
  rw [he] at h
  exact h

theorem hasDerivAt_dirichletLeftReal_deriv
    (t x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        -Real.cosh ((t - y) / 2) / (2 * Real.sinh t))
      ((1 / 4 : ℝ) * dirichletLeftReal t x)
      x := by
  have hinner : HasDerivAt (fun y : ℝ => (t - y) / 2) (-1 / 2 : ℝ) x := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      ((hasDerivAt_const x t).sub (hasDerivAt_id x)).div_const 2
  have h := hinner.cosh.neg.div_const (2 * Real.sinh t)
  have he : (-(Real.sinh ((t - x) / 2) * (-1 / 2))) / (2 * Real.sinh t) =
      (1 / 4 : ℝ) * dirichletLeftReal t x := by
    unfold dirichletLeftReal
    ring
  rw [he] at h
  exact h

theorem hasDerivAt_dirichletRightBasis
    (t x : ℝ) :
    HasDerivAt
      (dirichletRightBasis t)
      ((Real.cosh ((t + x) / 2) / (2 * Real.sinh t) : ℝ) : ℂ)
      x := by
  change HasDerivAt
    (fun y : ℝ => (dirichletRightReal t y : ℂ))
    ((Real.cosh ((t + x) / 2) / (2 * Real.sinh t) : ℝ) : ℂ) x
  exact (hasDerivAt_dirichletRightReal t x).ofReal_comp

theorem hasDerivAt_dirichletLeftBasis
    (t x : ℝ) :
    HasDerivAt
      (dirichletLeftBasis t)
      ((-Real.cosh ((t - x) / 2) / (2 * Real.sinh t) : ℝ) : ℂ)
      x := by
  change HasDerivAt
    (fun y : ℝ => (dirichletLeftReal t y : ℂ))
    ((-Real.cosh ((t - x) / 2) / (2 * Real.sinh t) : ℝ) : ℂ) x
  exact (hasDerivAt_dirichletLeftReal t x).ofReal_comp

theorem iteratedDeriv_two_dirichletRightBasis
    (t x : ℝ) :
    iteratedDeriv 2 (dirichletRightBasis t) x =
      (1 / 4 : ℂ) * dirichletRightBasis t x := by
  have h1 :
      deriv (dirichletRightBasis t) =
        fun y : ℝ =>
          ((Real.cosh ((t + y) / 2) / (2 * Real.sinh t) : ℝ) : ℂ) := by
    funext y
    exact (hasDerivAt_dirichletRightBasis t y).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
  have h2 :=
    (hasDerivAt_dirichletRightReal_deriv t x).ofReal_comp
  simpa [dirichletRightBasis] using h2.deriv

theorem iteratedDeriv_two_dirichletLeftBasis
    (t x : ℝ) :
    iteratedDeriv 2 (dirichletLeftBasis t) x =
      (1 / 4 : ℂ) * dirichletLeftBasis t x := by
  have h1 :
      deriv (dirichletLeftBasis t) =
        fun y : ℝ =>
          ((-Real.cosh ((t - y) / 2) / (2 * Real.sinh t) : ℝ) : ℂ) := by
    funext y
    exact (hasDerivAt_dirichletLeftBasis t y).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
  have h2 :=
    (hasDerivAt_dirichletLeftReal_deriv t x).ofReal_comp
  simpa [dirichletLeftBasis] using h2.deriv

theorem problemOneL_dirichletRightBasis (t x : ℝ) :
    problemOneL (dirichletRightBasis t) x = 0 := by
  rw [problemOneL, iteratedDeriv_two_dirichletRightBasis]
  ring

theorem problemOneL_dirichletLeftBasis (t x : ℝ) :
    problemOneL (dirichletLeftBasis t) x = 0 := by
  rw [problemOneL, iteratedDeriv_two_dirichletLeftBasis]
  ring

theorem dirichletProblemOneColumn_pos
    (t : ℝ) (gamma : ℂ) (ht : t ≠ 0) :
    dirichletProblemOneColumn t gamma t = 0 := by
  simp [dirichletProblemOneColumn,
    dirichletRightBasis_pos t ht, dirichletLeftBasis_pos]

theorem dirichletProblemOneColumn_neg
    (t : ℝ) (gamma : ℂ) (ht : t ≠ 0) :
    dirichletProblemOneColumn t gamma (-t) = 0 := by
  simp [dirichletProblemOneColumn,
    dirichletRightBasis_neg, dirichletLeftBasis_neg t ht]

theorem contDiffAt_dirichletRightBasis
    (k : ℕ) (t x : ℝ) :
    ContDiffAt ℝ k (dirichletRightBasis t) x := by
  have hreal : ContDiffAt ℝ k (dirichletRightReal t) x := by
    unfold dirichletRightReal
    fun_prop
  have hcoe :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  change ContDiffAt ℝ k
    (Complex.ofRealCLM ∘ dirichletRightReal t) x
  exact hcoe

theorem contDiffAt_dirichletLeftBasis
    (k : ℕ) (t x : ℝ) :
    ContDiffAt ℝ k (dirichletLeftBasis t) x := by
  have hreal : ContDiffAt ℝ k (dirichletLeftReal t) x := by
    unfold dirichletLeftReal
    fun_prop
  have hcoe :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  change ContDiffAt ℝ k
    (Complex.ofRealCLM ∘ dirichletLeftReal t) x
  exact hcoe

theorem problemOneL_dirichletProblemOneColumn
    (t x : ℝ) (gamma : ℂ)
    (hden : problemOneGreenDenom gamma ≠ 0) :
    problemOneL (dirichletProblemOneColumn t gamma) x =
      realExpMode (problemOneFreq gamma) x := by
  let q := problemOneGreenQ gamma
  let f0 : ℝ → ℂ :=
    fun y => q * realExpMode (problemOneFreq gamma) y
  let fR : ℝ → ℂ :=
    fun y =>
      (-q * realExpMode (problemOneFreq gamma) t) * dirichletRightBasis t y
  let fL : ℝ → ℂ :=
    fun y =>
      (-q * realExpMode (problemOneFreq gamma) (-t)) * dirichletLeftBasis t y
  have hq :
      q * problemOneDenominator (problemOneFreq gamma) = 1 := by
    dsimp [q, problemOneGreenQ]
    rw [problemOneDenominator_problemOneFreq]
    exact inv_mul_cancel₀ hden
  have hf0 : ContDiffAt ℝ 2 f0 x := by
    simpa [f0] using
      contDiffAt_const_mul_realExpMode 2 q (problemOneFreq gamma) x
  have hfR : ContDiffAt ℝ 2 fR x := by
    exact (contDiff_const.contDiffAt.mul
      (contDiffAt_dirichletRightBasis 2 t x))
  have hfL : ContDiffAt ℝ 2 fL x := by
    exact (contDiff_const.contDiffAt.mul
      (contDiffAt_dirichletLeftBasis 2 t x))
  have hcol :
      dirichletProblemOneColumn t gamma = f0 + fR + fL := by
    funext y
    rfl
  rw [hcol]
  rw [problemOneL_add (f0 + fR) fL x (hf0.add hfR) hfL]
  rw [problemOneL_add f0 fR x hf0 hfR]
  have h0 :
      problemOneL f0 x =
        realExpMode (problemOneFreq gamma) x := by
    rw [show f0 =
      fun y => q * realExpMode (problemOneFreq gamma) y by rfl]
    rw [problemOneL_const_mul_realExpMode, hq, one_mul]
  have hR : problemOneL fR x = 0 := by
    rw [show fR =
      fun y => (-q * realExpMode (problemOneFreq gamma) t) *
        dirichletRightBasis t y by rfl]
    rw [problemOneL_const_mul, problemOneL_dirichletRightBasis, mul_zero]
  have hL : problemOneL fL x = 0 := by
    rw [show fL =
      fun y => (-q * realExpMode (problemOneFreq gamma) (-t)) *
        dirichletLeftBasis t y by rfl]
    rw [problemOneL_const_mul, problemOneL_dirichletLeftBasis, mul_zero]
  rw [h0, hR, hL, add_zero, add_zero]

theorem contDiff_dirichletProblemOneColumn
    (t : ℝ) (gamma : ℂ) :
    ContDiff ℝ 2 (dirichletProblemOneColumn t gamma) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let q := problemOneGreenQ gamma
  let f0 : ℝ → ℂ :=
    fun y => q * realExpMode (problemOneFreq gamma) y
  let fR : ℝ → ℂ :=
    fun y =>
      (-q * realExpMode (problemOneFreq gamma) t) *
        dirichletRightBasis t y
  let fL : ℝ → ℂ :=
    fun y =>
      (-q * realExpMode (problemOneFreq gamma) (-t)) *
        dirichletLeftBasis t y
  have hf0 : ContDiffAt ℝ 2 f0 x := by
    simpa [f0] using
      contDiffAt_const_mul_realExpMode 2 q (problemOneFreq gamma) x
  have hfR : ContDiffAt ℝ 2 fR x := by
    exact
      (contDiff_const.contDiffAt.mul
        (contDiffAt_dirichletRightBasis 2 t x))
  have hfL : ContDiffAt ℝ 2 fL x := by
    exact
      (contDiff_const.contDiffAt.mul
        (contDiffAt_dirichletLeftBasis 2 t x))
  have hcol :
      dirichletProblemOneColumn t gamma = f0 + fR + fL := by
    funext y
    rfl
  rw [hcol]
  exact (hf0.add hfR).add hfL

end WeilDefect

namespace WeilDefect.ConnesNative
open WeilDefect
def dirichletTestAnalysis (t : ℝ) (γ : ℂ) (g : ℝ → ℂ) : ℂ :=
  ∫ x in -t..t,
    star (iteratedDeriv 1 (dirichletProblemOneColumn t γ) x) * iteratedDeriv 1 g x +
      (1 / 4 : ℂ) * star (dirichletProblemOneColumn t γ x) * g x

theorem dirichletTestAnalysis_eq_source (t : ℝ) (_ht : 0 < t)
    (γ : ℂ) (hden : problemOneGreenDenom γ ≠ 0)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    dirichletTestAnalysis t γ g =
      ∫ x in -t..t, star (realExpMode (problemOneFreq γ) x) * g x := by
  let F := dirichletProblemOneColumn t γ
  let dF := iteratedDeriv 1 F
  let ddF := iteratedDeriv 2 F
  let dg := iteratedDeriv 1 g
  have hF : ContDiff ℝ 2 F := contDiff_dirichletProblemOneColumn t γ
  have hdF : Continuous dF := hF.continuous_iteratedDeriv 1 (by norm_num)
  have hddF : Continuous ddF := hF.continuous_iteratedDeriv 2 (by norm_num)
  have hgc : Continuous g := hg.1.1.continuous
  have hdg : Continuous dg := hg.1.1.continuous_iteratedDeriv 1 (by simp)
  have hgder : ∀ x, HasDerivAt g (dg x) x := by
    intro x
    simpa [dg, iteratedDeriv_one] using
      (hg.1.1.differentiable (by simp) x).hasDerivAt
  have hFder : ∀ x, HasDerivAt dF (ddF x) x := by
    intro x
    have h := (hF.differentiable_iteratedDeriv 1 (by norm_num) x).hasDerivAt
    simpa [dF, ddF, iteratedDeriv_succ] using h
  have hb : g t = 0 ∧ g (-t) = 0 := by
    constructor <;> by_contra hn
    · have h := hg.2 (subset_tsupport g hn)
      exact (lt_irrefl t) h.2
    · have h := hg.2 (subset_tsupport g hn)
      exact (lt_irrefl (-t)) h.1
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -t) (b := t) (u := fun x => star (dF x)) (v := g)
    (u' := fun x => star (ddF x)) (v' := dg)
    hdF.star.continuousOn hgc.continuousOn
    (fun x _ => (hFder x).star) (fun x _ => hgder x)
    (hddF.star.intervalIntegrable (-t) t) (hdg.intervalIntegrable (-t) t)
  simp only [hb.1, hb.2, mul_zero, sub_zero, zero_sub] at hip
  have hmass : IntervalIntegrable (fun x => (1 / 4 : ℂ) * star (F x) * g x)
      volume (-t) t :=
    ((continuous_const.mul hF.continuous.star).mul hgc).intervalIntegrable _ _
  have hdd : IntervalIntegrable (fun x => star (ddF x) * g x) volume (-t) t :=
    (hddF.star.mul hgc).intervalIntegrable _ _
  have hgrad : IntervalIntegrable (fun x => star (dF x) * dg x) volume (-t) t :=
    (hdF.star.mul hdg).intervalIntegrable _ _
  have hsrc : ∀ x, star (realExpMode (problemOneFreq γ) x) * g x =
      -(star (ddF x) * g x) + (1 / 4 : ℂ) * star (F x) * g x := by
    intro x
    have h := (problemOneL_dirichletProblemOneColumn t x γ hden).symm
    change realExpMode (problemOneFreq γ) x = -ddF x + (1 / 4 : ℂ) * F x at h
    rw [h]
    simp
    ring
  unfold dirichletTestAnalysis
  change (∫ x in -t..t, star (dF x) * dg x + (1 / 4 : ℂ) * star (F x) * g x) = _
  rw [intervalIntegral.integral_add hgrad hmass, hip]
  rw [intervalIntegral.integral_congr (fun x _ => hsrc x)]
  simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using
    (intervalIntegral.integral_add hdd.neg hmass).symm

theorem reflected_ordinate_denominator_ne_zero (z : ℂ) (hz : IsCriticalZero z) :
    problemOneGreenDenom (-I * (mirror z - 1 / 2)) ≠ 0 := by
  have hfactor : problemOneGreenDenom (-I * (mirror z - 1 / 2)) =
      star z * (1 - star z) := by
    simp [problemOneGreenDenom, mirror, mul_pow, Complex.I_sq]
    ring
  rw [hfactor]
  apply mul_ne_zero
  · intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith [hz.2.1]
  · intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith [hz.2.2]

theorem dirichlet_source_pairing_eq_analysis (t : ℝ) (ht : 0 < t)
    (γ : ℂ) (g : ℝ → ℂ) (hg : IsTest g) :
    (∫ x in -t..t, star (dirichletProblemOneColumn t γ x) * problemOneL g x) =
      dirichletTestAnalysis t γ g := by
  let F := dirichletProblemOneColumn t γ
  let dF := iteratedDeriv 1 F
  let dg := iteratedDeriv 1 g
  let ddg := iteratedDeriv 2 g
  have hF := contDiff_dirichletProblemOneColumn t γ
  have hdF : Continuous dF := hF.continuous_iteratedDeriv 1 (by norm_num)
  have hdg : Continuous dg := hg.1.continuous_iteratedDeriv 1 (by simp)
  have hddg : Continuous ddg := hg.1.continuous_iteratedDeriv 2 (by norm_cast <;> simp)
  have hFder : ∀ x, HasDerivAt F (dF x) x := by
    intro x
    simpa [dF, iteratedDeriv_one] using (hF.differentiable (by norm_num) x).hasDerivAt
  have hgder : ∀ x, HasDerivAt dg (ddg x) x := by
    intro x
    simpa [dg, ddg, iteratedDeriv_succ] using
      (hg.1.differentiable_iteratedDeriv 1 (by simp) x).hasDerivAt
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -t) (b := t) (u := fun x => star (F x)) (v := dg)
    (u' := fun x => star (dF x)) (v' := ddg)
    hF.continuous.star.continuousOn hdg.continuousOn
    (fun x _ => (hFder x).star) (fun x _ => hgder x)
    (hdF.star.intervalIntegrable (-t) t) (hddg.intervalIntegrable (-t) t)
  have hb : F t = 0 ∧ F (-t) = 0 :=
    ⟨dirichletProblemOneColumn_pos t γ ht.ne', dirichletProblemOneColumn_neg t γ ht.ne'⟩
  simp only [hb.1, hb.2, star_zero, zero_mul, sub_zero, zero_sub] at hip
  have hmass : IntervalIntegrable (fun x => (1 / 4 : ℂ) * star (F x) * g x)
      volume (-t) t :=
    ((continuous_const.mul hF.continuous.star).mul hg.1.continuous).intervalIntegrable _ _
  have hdd : IntervalIntegrable (fun x => star (F x) * ddg x) volume (-t) t :=
    (hF.continuous.star.mul hddg).intervalIntegrable _ _
  have hgrad : IntervalIntegrable (fun x => star (dF x) * dg x) volume (-t) t :=
    (hdF.star.mul hdg).intervalIntegrable _ _
  have heq : ∀ x, star (F x) * problemOneL g x =
      -(star (F x) * ddg x) + (1 / 4 : ℂ) * star (F x) * g x := by
    intro x
    simp [problemOneL, ddg]
    ring
  rw [intervalIntegral.integral_congr (fun x _ => heq x)]
  have hadd := intervalIntegral.integral_add hdd.neg hmass
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hadd
  rw [hadd, hip, neg_neg]
  exact (intervalIntegral.integral_add hgrad hmass).symm

theorem problemOneL_supported (t : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    SupportedTest t (problemOneL g) := by
  have hd : iteratedDeriv 2 g = deriv (deriv g) := by
    simp [iteratedDeriv_succ, iteratedDeriv_one]
  have hs : tsupport (iteratedDeriv 2 g) ⊆ tsupport g := by
    rw [hd]
    exact tsupport_deriv_subset.trans tsupport_deriv_subset
  have hcompact : HasCompactSupport (iteratedDeriv 2 g) := by
    rw [hd]
    exact hg.1.2.deriv.deriv
  have hts : tsupport (problemOneL g) ⊆ tsupport g := by
    apply closure_minimal ?_ (isClosed_tsupport g)
    intro x hx
    by_contra hn
    have h0 := image_eq_zero_of_notMem_tsupport hn
    have h2 := image_eq_zero_of_notMem_tsupport (fun h => hn (hs h))
    exact hx (by simp [problemOneL, h0, h2])
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hder : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 2 g) := by
      rw [hd]
      exact (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hg.1.1).2).2
    exact hder.neg.add (contDiff_const.mul hg.1.1)
  · exact hcompact.neg.add hg.1.2.mul_left
  · exact hts.trans hg.2

end WeilDefect.ConnesNative


namespace WeilDefect
attribute [local instance 1100] NormedSpace.complexToReal
open Filter Set Bornology
theorem norm_dirichletRightBasis_le_one
    (t x : ℝ) (ht : 0 < t)
    (hx : x ∈ Set.Icc (-t) t) :
    ‖dirichletRightBasis t x‖ ≤ 1 := by
  have hspos : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have ha0 : 0 ≤ (t + x) / 2 := by linarith [hx.1]
  have hat : (t + x) / 2 ≤ t := by linarith [hx.2]
  have hs0 : 0 ≤ Real.sinh ((t + x) / 2) :=
    Real.sinh_nonneg_iff.mpr ha0
  have hsle :
      Real.sinh ((t + x) / 2) ≤ Real.sinh t :=
    Real.sinh_le_sinh.mpr hat
  have hdiv :
      Real.sinh ((t + x) / 2) / Real.sinh t ≤ 1 := by
    rw [div_le_one hspos]
    exact hsle
  rw [dirichletRightBasis, Complex.ofRealCLM_apply,
    Complex.norm_real, Real.norm_eq_abs]
  rw [dirichletRightReal, abs_of_nonneg (div_nonneg hs0 hspos.le)]
  exact hdiv

theorem norm_dirichletLeftBasis_le_one
    (t x : ℝ) (ht : 0 < t)
    (hx : x ∈ Set.Icc (-t) t) :
    ‖dirichletLeftBasis t x‖ ≤ 1 := by
  have hspos : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  have ha0 : 0 ≤ (t - x) / 2 := by linarith [hx.2]
  have hat : (t - x) / 2 ≤ t := by linarith [hx.1]
  have hs0 : 0 ≤ Real.sinh ((t - x) / 2) :=
    Real.sinh_nonneg_iff.mpr ha0
  have hsle :
      Real.sinh ((t - x) / 2) ≤ Real.sinh t :=
    Real.sinh_le_sinh.mpr hat
  have hdiv :
      Real.sinh ((t - x) / 2) / Real.sinh t ≤ 1 := by
    rw [div_le_one hspos]
    exact hsle
  rw [dirichletLeftBasis, Complex.ofRealCLM_apply,
    Complex.norm_real, Real.norm_eq_abs]
  rw [dirichletLeftReal, abs_of_nonneg (div_nonneg hs0 hspos.le)]
  exact hdiv

theorem problemOneGreenDenom_re_lower
    (gamma : ℂ)
    (hstrip : |gamma.im| ≤ 1 / 2) :
    gamma.re ^ 2 ≤ (problemOneGreenDenom gamma).re := by
  have himlo : -(1 / 2 : ℝ) ≤ gamma.im := (abs_le.mp hstrip).1
  have himhi : gamma.im ≤ (1 / 2 : ℝ) := (abs_le.mp hstrip).2
  simp [problemOneGreenDenom, pow_two, Complex.mul_re]
  nlinarith

theorem problemOneGreenDenom_norm_lower
    (gamma : ℂ)
    (hstrip : |gamma.im| ≤ 1 / 2) :
    gamma.re ^ 2 ≤ ‖problemOneGreenDenom gamma‖ := by
  calc
    gamma.re ^ 2
        ≤ (problemOneGreenDenom gamma).re :=
      problemOneGreenDenom_re_lower gamma hstrip
    _ ≤ |(problemOneGreenDenom gamma).re| := le_abs_self _
    _ ≤ ‖problemOneGreenDenom gamma‖ := Complex.abs_re_le_norm _

theorem norm_problemOne_source_le
    (t x : ℝ) (gamma : ℂ)
    (ht : 0 ≤ t)
    (hstrip : |gamma.im| ≤ 1 / 2)
    (hx : x ∈ Set.Icc (-t) t) :
    ‖realExpMode (problemOneFreq gamma) x‖
      ≤ Real.exp (t / 2) := by
  have hxabs : |x| ≤ t := by
    rw [abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  have himabs : |gamma.im| ≤ (1 / 2 : ℝ) := hstrip
  have hmul : x * gamma.im ≤ t / 2 := by
    calc
      x * gamma.im ≤ |x * gamma.im| := le_abs_self _
      _ = |x| * |gamma.im| := abs_mul _ _
      _ ≤ t * (1 / 2 : ℝ) := by gcongr
      _ = t / 2 := by ring
  simp only [realExpMode, problemOneFreq, Complex.norm_exp]
  apply Real.exp_monotone
  simp [Complex.mul_re, Complex.mul_im]
  ring_nf at *
  exact hmul

theorem norm_dirichletProblemOneColumn_le
    (t x : ℝ) (gamma : ℂ)
    (ht : 0 < t)
    (hstrip : |gamma.im| ≤ 1 / 2)
    (hx : x ∈ Set.Icc (-t) t) :
    ‖dirichletProblemOneColumn t gamma x‖
      ≤
    3 * Real.exp (t / 2) * ‖problemOneGreenQ gamma‖ := by
  have hsx :=
    norm_problemOne_source_le t x gamma ht.le hstrip hx
  have hst :
      ‖realExpMode (problemOneFreq gamma) t‖ ≤ Real.exp (t / 2) := by
    apply norm_problemOne_source_le t t gamma ht.le hstrip
    exact ⟨by linarith, le_rfl⟩
  have hsnt :
      ‖realExpMode (problemOneFreq gamma) (-t)‖ ≤ Real.exp (t / 2) := by
    apply norm_problemOne_source_le t (-t) gamma ht.le hstrip
    exact ⟨le_rfl, by linarith⟩
  have hR := norm_dirichletRightBasis_le_one t x ht hx
  have hL := norm_dirichletLeftBasis_le_one t x ht hx
  unfold dirichletProblemOneColumn
  calc
    ‖problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) x
        + (-problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) t) *
            dirichletRightBasis t x
        + (-problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) (-t)) *
            dirichletLeftBasis t x‖
        ≤
      ‖problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) x‖
        + ‖(-problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) t) *
            dirichletRightBasis t x‖
        + ‖(-problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) (-t)) *
            dirichletLeftBasis t x‖ := by
          calc
            ‖(problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) x
                + (-problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) t) *
                    dirichletRightBasis t x)
                + (-problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) (-t)) *
                    dirichletLeftBasis t x‖
                ≤
              ‖problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) x
                + (-problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) t) *
                    dirichletRightBasis t x‖
                + ‖(-problemOneGreenQ gamma *
                    realExpMode (problemOneFreq gamma) (-t)) *
                    dirichletLeftBasis t x‖ := norm_add_le _ _
            _ ≤
              (‖problemOneGreenQ gamma * realExpMode (problemOneFreq gamma) x‖
                + ‖(-problemOneGreenQ gamma *
                    realExpMode (problemOneFreq gamma) t) *
                    dirichletRightBasis t x‖)
                + ‖(-problemOneGreenQ gamma *
                    realExpMode (problemOneFreq gamma) (-t)) *
                    dirichletLeftBasis t x‖ := by
                  gcongr
                  exact norm_add_le _ _
    _ ≤
      ‖problemOneGreenQ gamma‖ * Real.exp (t / 2)
        + (‖problemOneGreenQ gamma‖ * Real.exp (t / 2)) * 1
        + (‖problemOneGreenQ gamma‖ * Real.exp (t / 2)) * 1 := by
      simp only [norm_mul, norm_neg]
      gcongr
    _ = 3 * Real.exp (t / 2) * ‖problemOneGreenQ gamma‖ := by
      ring

noncomputable def problemOneGreenPairing
    (t : ℝ) (gamma : ℂ) : ℂ :=
  ∫ x in -t..t,
    star (realExpMode (problemOneFreq gamma) x) *
      dirichletProblemOneColumn t gamma x

noncomputable def problemOneColumnEnergySq
    (t : ℝ) (gamma : ℂ) : ℝ :=
  ‖problemOneGreenPairing t gamma‖

theorem problemOneColumnEnergySq_le
    (t : ℝ) (gamma : ℂ)
    (ht : 0 < t)
    (hstrip : |gamma.im| ≤ 1 / 2) :
    problemOneColumnEnergySq t gamma
      ≤
    (6 * t * (Real.exp (t / 2)) ^ 2) *
      ‖problemOneGreenQ gamma‖ := by
  let E : ℝ := Real.exp (t / 2)
  have hpoint :
      ∀ x ∈ Ι (-t) t,
        ‖star (realExpMode (problemOneFreq gamma) x) *
            dirichletProblemOneColumn t gamma x‖
          ≤ 3 * E ^ 2 * ‖problemOneGreenQ gamma‖ := by
    intro x hx
    have hle : -t ≤ t := by linarith
    have hxioc : x ∈ Set.Ioc (-t) t := by
      simpa [uIoc_of_le hle] using hx
    have hxIcc : x ∈ Set.Icc (-t) t :=
      ⟨hxioc.1.le, hxioc.2⟩
    have hs :=
      norm_problemOne_source_le t x gamma ht.le hstrip hxIcc
    have hF :=
      norm_dirichletProblemOneColumn_le t x gamma ht hstrip hxIcc
    simp only [norm_mul, norm_star]
    calc
      ‖realExpMode (problemOneFreq gamma) x‖ *
          ‖dirichletProblemOneColumn t gamma x‖
          ≤ E * (3 * E * ‖problemOneGreenQ gamma‖) := by
            gcongr
      _ = 3 * E ^ 2 * ‖problemOneGreenQ gamma‖ := by ring
  unfold problemOneColumnEnergySq problemOneGreenPairing
  calc
    ‖∫ x in -t..t,
      star (realExpMode (problemOneFreq gamma) x) *
        dirichletProblemOneColumn t gamma x‖
        ≤
      (3 * E ^ 2 * ‖problemOneGreenQ gamma‖) * |t - (-t)| := by
        exact intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (6 * t * E ^ 2) * ‖problemOneGreenQ gamma‖ := by
      rw [abs_of_nonneg (by linarith : 0 ≤ t - (-t))]
      ring
    _ = (6 * t * (Real.exp (t / 2)) ^ 2) *
        ‖problemOneGreenQ gamma‖ := by rfl

noncomputable def problemOneDirichletEnergyComplex
    (t : ℝ) (gamma : ℂ) : ℂ :=
  ∫ x in -t..t,
    star (iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x) *
        iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x
      + (1 / 4 : ℂ) *
        star (dirichletProblemOneColumn t gamma x) *
        dirichletProblemOneColumn t gamma x

theorem dirichlet_second_derivative_pairing
    (t : ℝ) (gamma : ℂ)
    (ht : 0 < t) :
    (∫ x in -t..t,
      star (iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x) *
        iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x)
      =
    -(∫ x in -t..t,
      star (iteratedDeriv 2 (dirichletProblemOneColumn t gamma) x) *
        dirichletProblemOneColumn t gamma x) := by
  let F : ℝ → ℂ := dirichletProblemOneColumn t gamma
  let dF : ℝ → ℂ := iteratedDeriv 1 F
  let ddF : ℝ → ℂ := iteratedDeriv 2 F
  have hF : ContDiff ℝ 2 F := by
    simpa [F] using contDiff_dirichletProblemOneColumn t gamma
  have hFcont : Continuous F := hF.continuous
  have hdFcont : Continuous dF := by
    dsimp [dF]
    exact hF.continuous_iteratedDeriv 1 (by norm_num)
  have hddFcont : Continuous ddF := by
    dsimp [ddF]
    exact hF.continuous_iteratedDeriv 2 (by norm_num)
  have hFdiff : Differentiable ℝ F := by
    have h0 :=
      hF.differentiable_iteratedDeriv 0 (by norm_num)
    simpa using h0
  have hdFdiff : Differentiable ℝ dF := by
    dsimp [dF]
    exact hF.differentiable_iteratedDeriv 1 (by norm_num)
  have hFder :
      ∀ x, HasDerivAt F (dF x) x := by
    intro x
    have hx := (hFdiff x).hasDerivAt
    simpa [dF, iteratedDeriv_one] using hx
  have hsucc : ddF = deriv dF := by
    dsimp [ddF, dF]
    simpa using
      (iteratedDeriv_succ
        (n := 1)
        (f := F))
  have hdFder :
      ∀ x, HasDerivAt dF (ddF x) x := by
    intro x
    have hx := (hdFdiff x).hasDerivAt
    rw [hsucc]
    exact hx
  have hucont :
      Continuous (fun x => star (dF x)) :=
    hdFcont.star
  have hudcont :
      Continuous (fun x => star (ddF x)) :=
    hddFcont.star
  have hip :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := -t) (b := t)
      (u := fun x => star (dF x))
      (v := F)
      (u' := fun x => star (ddF x))
      (v' := dF)
      hucont.continuousOn
      hFcont.continuousOn
      (fun x _ => (hdFder x).star)
      (fun x _ => hFder x)
      (hudcont.intervalIntegrable (-t) t)
      (hdFcont.intervalIntegrable (-t) t)
  have hFt : F t = 0 := by
    simpa [F] using
      dirichletProblemOneColumn_pos t gamma ht.ne'
  have hFnt : F (-t) = 0 := by
    simpa [F] using
      dirichletProblemOneColumn_neg t gamma ht.ne'
  have hip' :
      (∫ x in -t..t, star (dF x) * dF x)
        =
      -(∫ x in -t..t, star (ddF x) * F x) := by
    simpa [hFt, hFnt] using hip
  simpa [F, dF, ddF] using hip'

theorem problemOneDirichletEnergyComplex_eq_ofReal
    (t : ℝ) (gamma : ℂ) :
    problemOneDirichletEnergyComplex t gamma
      =
    (problemOneDirichletEnergy t gamma : ℂ) := by
  unfold problemOneDirichletEnergyComplex problemOneDirichletEnergy
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  have hstar (z : ℂ) :
      star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    simpa [RCLike.star_def] using Complex.conj_mul' z
  change
    star (iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x) *
          iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x
        + (1 / 4 : ℂ) *
          star (dirichletProblemOneColumn t gamma x) *
          dirichletProblemOneColumn t gamma x
      =
    ((‖iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x‖ ^ 2
        + (1 / 4 : ℝ) *
          ‖dirichletProblemOneColumn t gamma x‖ ^ 2 : ℝ) : ℂ)
  rw [hstar (iteratedDeriv 1 (dirichletProblemOneColumn t gamma) x)]
  rw [mul_assoc, hstar (dirichletProblemOneColumn t gamma x)]
  push_cast
  rfl

theorem problemOneDirichletEnergy_nonneg
    (t : ℝ) (gamma : ℂ)
    (ht : 0 ≤ t) :
    0 ≤ problemOneDirichletEnergy t gamma := by
  unfold problemOneDirichletEnergy
  apply intervalIntegral.integral_nonneg
  · linarith
  · intro x hx
    positivity

theorem problemOneGreenPairing_eq_dirichletEnergyComplex
    (t : ℝ) (gamma : ℂ)
    (ht : 0 < t)
    (hden : problemOneGreenDenom gamma ≠ 0) :
    problemOneGreenPairing t gamma
      =
    problemOneDirichletEnergyComplex t gamma := by
  let F : ℝ → ℂ := dirichletProblemOneColumn t gamma
  let dF : ℝ → ℂ := iteratedDeriv 1 F
  let ddF : ℝ → ℂ := iteratedDeriv 2 F
  have hF : ContDiff ℝ 2 F := by
    simpa [F] using contDiff_dirichletProblemOneColumn t gamma
  have hFcont : Continuous F := hF.continuous
  have hdFcont : Continuous dF := by
    dsimp [dF]
    exact hF.continuous_iteratedDeriv 1 (by norm_num)
  have hddFcont : Continuous ddF := by
    dsimp [ddF]
    exact hF.continuous_iteratedDeriv 2 (by norm_num)
  have hsrc :
      ∀ x,
        realExpMode (problemOneFreq gamma) x
          =
        -ddF x + (1 / 4 : ℂ) * F x := by
    intro x
    have h :=
      (problemOneL_dirichletProblemOneColumn
        t x gamma hden).symm
    simpa [F, ddF, problemOneL] using h
  have hintegrand :
      ∀ x,
        star (realExpMode (problemOneFreq gamma) x) * F x
          =
        -(star (ddF x) * F x)
          + (1 / 4 : ℂ) * star (F x) * F x := by
    intro x
    rw [hsrc x]
    simp
    ring
  have hddprod :
      Continuous (fun x => star (ddF x) * F x) :=
    hddFcont.star.mul hFcont
  have hgradprod :
      Continuous (fun x => star (dF x) * dF x) :=
    hdFcont.star.mul hdFcont
  have hmassprod :
      Continuous
        (fun x =>
          (1 / 4 : ℂ) * star (F x) * F x) :=
    (continuous_const.mul hFcont.star).mul hFcont
  have hibp :=
    dirichlet_second_derivative_pairing t gamma ht
  unfold problemOneGreenPairing
  unfold problemOneDirichletEnergyComplex
  calc
    (∫ x in -t..t,
      star (realExpMode (problemOneFreq gamma) x) * F x)
        =
      ∫ x in -t..t,
        (-(star (ddF x) * F x)
          + (1 / 4 : ℂ) * star (F x) * F x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hintegrand x
    _ =
      -(∫ x in -t..t, star (ddF x) * F x)
        +
      ∫ x in -t..t,
        (1 / 4 : ℂ) * star (F x) * F x := by
          have hnegInt :
              IntervalIntegrable
                (fun x => -(star (ddF x) * F x))
                volume (-t) t :=
            hddprod.neg.intervalIntegrable (-t) t
          have hmassInt :
              IntervalIntegrable
                (fun x => (1 / 4 : ℂ) * star (F x) * F x)
                volume (-t) t :=
            hmassprod.intervalIntegrable (-t) t
          rw [intervalIntegral.integral_add hnegInt hmassInt]
          rw [intervalIntegral.integral_neg]
    _ =
      (∫ x in -t..t, star (dF x) * dF x)
        +
      ∫ x in -t..t,
        (1 / 4 : ℂ) * star (F x) * F x := by
          have hibp' :
              (∫ x in -t..t, star (dF x) * dF x)
                =
              -(∫ x in -t..t, star (ddF x) * F x) := by
            simpa [F, dF, ddF] using hibp
          rw [← hibp']
    _ =
      ∫ x in -t..t,
        (star (dF x) * dF x
          + (1 / 4 : ℂ) * star (F x) * F x) := by
          have hgradInt :
              IntervalIntegrable
                (fun x => star (dF x) * dF x)
                volume (-t) t :=
            hgradprod.intervalIntegrable (-t) t
          have hmassInt :
              IntervalIntegrable
                (fun x => (1 / 4 : ℂ) * star (F x) * F x)
                volume (-t) t :=
            hmassprod.intervalIntegrable (-t) t
          rw [intervalIntegral.integral_add hgradInt hmassInt]

theorem problemOneGreenPairing_eq_dirichletEnergy
    (t : ℝ) (gamma : ℂ)
    (ht : 0 < t)
    (hden : problemOneGreenDenom gamma ≠ 0) :
    problemOneGreenPairing t gamma
      =
    (problemOneDirichletEnergy t gamma : ℂ) := by
  rw [
    problemOneGreenPairing_eq_dirichletEnergyComplex
      t gamma ht hden,
    problemOneDirichletEnergyComplex_eq_ofReal
  ]

theorem problemOneColumnEnergySq_eq_dirichletEnergy
    (t : ℝ) (gamma : ℂ)
    (ht : 0 < t)
    (hden : problemOneGreenDenom gamma ≠ 0) :
    problemOneColumnEnergySq t gamma
      =
    problemOneDirichletEnergy t gamma := by
  rw [problemOneColumnEnergySq,
    problemOneGreenPairing_eq_dirichletEnergy t gamma ht hden]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (problemOneDirichletEnergy_nonneg t gamma ht.le)]

end WeilDefect

namespace WeilDefect.ConnesNative
open WeilDefect
theorem actualGreenOrdinate_re (ρ : CriticalZeros) :
    (actualGreenOrdinate ρ).re = ρ.1.im := by
  simp [actualGreenOrdinate, mirror]

theorem actualGreenOrdinate_im (ρ : CriticalZeros) :
    (actualGreenOrdinate ρ).im = ρ.1.re - 1 / 2 := by
  simp [actualGreenOrdinate, mirror]
  ring

theorem actualGreenOrdinate_strip (ρ : CriticalZeros) :
    |(actualGreenOrdinate ρ).im| ≤ 1 / 2 := by
  rw [actualGreenOrdinate_im, abs_le]
  constructor <;> linarith [ρ.2.2.1, ρ.2.2.2]

theorem actual_unreflected_gamma_normSq (ρ : CriticalZeros) :
    Complex.normSq ((ρ.1 - 1 / 2) / I) =
      ρ.1.im ^ 2 + (ρ.1.re - 1 / 2) ^ 2 := by
  have heq : (ρ.1 - 1 / 2) / I = -I * (ρ.1 - 1 / 2) := by
    simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  simp [Complex.normSq_apply]
  ring

theorem actual_low_weighted_height_finite :
    {ρ : CriticalZeros | |ρ.1.im| < 1 ∧ zeroMult ρ.1 ≠ 0}.Finite := by
  have hs : Summable (fun ρ : CriticalZeros => (zeroMult ρ.1 : ℝ) /
      (1 + Complex.normSq ((ρ.1 - 1 / 2) / I))) :=
    actual_zero_reciprocal_square_summable
  have he := hs.tendsto_cofinite_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  have hf : {ρ : CriticalZeros | (1 / 3 : ℝ) ≤ (zeroMult ρ.1 : ℝ) /
      (1 + Complex.normSq ((ρ.1 - 1 / 2) / I))}.Finite := by
    simpa only [Filter.eventually_cofinite, not_lt] using he
  apply hf.subset
  intro ρ hρ
  have hm : (1 : ℝ) ≤ zeroMult ρ.1 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hρ.2
  have hi : ρ.1.im ^ 2 ≤ (1 : ℝ) := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr hρ.1.le
    simpa using hh
  have hr : (ρ.1.re - 1 / 2) ^ 2 ≤ (1 / 4 : ℝ) := by
    have ha : |ρ.1.re - 1 / 2| ≤ (1 / 2 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith [ρ.2.2.1, ρ.2.2.2]
    have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr ha
    norm_num at hh ⊢
    exact hh
  have hp : 0 < 1 + Complex.normSq ((ρ.1 - 1 / 2) / I) := by
    linarith [Complex.normSq_nonneg ((ρ.1 - 1 / 2) / I)]
  have hb : 1 + Complex.normSq ((ρ.1 - 1 / 2) / I) ≤ 3 := by
    rw [actual_unreflected_gamma_normSq]
    nlinarith
  exact (le_div_iff₀ hp).mpr (by nlinarith)


theorem actual_Green_reciprocal_high_bound (ρ : CriticalZeros)
    (hheight : 1 ≤ |ρ.1.im|) :
    ‖problemOneGreenQ (actualGreenOrdinate ρ)‖ ≤
      3 / (1 + Complex.normSq (((ρ.1 - 1 / 2) / I))) := by
  have hd := problemOneGreenDenom_norm_lower (actualGreenOrdinate ρ)
    (actualGreenOrdinate_strip ρ)
  rw [actualGreenOrdinate_re] at hd
  have hi : (1 : ℝ) ≤ ρ.1.im ^ 2 := by
    have hh := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg _)).mpr hheight
    simpa using hh
  have hr : (ρ.1.re - 1 / 2) ^ 2 ≤ (1 / 4 : ℝ) := by
    have ha : |ρ.1.re - 1 / 2| ≤ (1 / 2 : ℝ) := by
      rw [abs_le]
      constructor <;> linarith [ρ.2.2.1, ρ.2.2.2]
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr ha
    norm_num at h ⊢
    exact h
  have hp : 0 < 1 + Complex.normSq (((ρ.1 - 1 / 2) / I)) := by
    linarith [Complex.normSq_nonneg (((ρ.1 - 1 / 2) / I))]
  have hb : 1 + Complex.normSq (((ρ.1 - 1 / 2) / I)) ≤ 3 * ρ.1.im ^ 2 := by
    rw [actual_unreflected_gamma_normSq]
    nlinarith
  have hdp : 0 < ‖problemOneGreenDenom (actualGreenOrdinate ρ)‖ := by linarith
  rw [problemOneGreenQ, norm_inv, inv_eq_one_div, div_le_div_iff₀ hdp hp]
  nlinarith

theorem actual_Green_reciprocal_summable :
    Summable (fun ρ : CriticalZeros => (zeroMult ρ.1 : ℝ) *
      ‖problemOneGreenQ (actualGreenOrdinate ρ)‖) := by
  classical
  let f := fun ρ : CriticalZeros => (zeroMult ρ.1 : ℝ) *
    ‖problemOneGreenQ (actualGreenOrdinate ρ)‖
  let low := fun ρ : CriticalZeros => if |ρ.1.im| < 1 then f ρ else 0
  let high := fun ρ : CriticalZeros => if |ρ.1.im| < 1 then 0 else f ρ
  have hl : Summable low := by
    apply summable_of_hasFiniteSupport
    apply actual_low_weighted_height_finite.subset
    intro ρ hρ
    by_cases hh : |ρ.1.im| < 1
    · refine ⟨hh, ?_⟩
      intro hz
      exact hρ (by simp [low, f, hz])
    · exact False.elim (hρ (by simp [low, hh]))
  have hh : Summable high := by
    apply Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_)
      (actual_zero_reciprocal_square_summable.mul_left 3)
    · dsimp [high, f]
      split_ifs <;> positivity
    · dsimp [high, f]
      by_cases h : |ρ.1.im| < 1
      · simp only [if_pos h]
        exact mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _)
          (by linarith [Complex.normSq_nonneg (((ρ.1 - 1 / 2) / I))]))
      · simp only [if_neg h]
        have hb := mul_le_mul_of_nonneg_left
          (actual_Green_reciprocal_high_bound ρ (le_of_not_gt h))
          (Nat.cast_nonneg (zeroMult ρ.1) : (0 : ℝ) ≤ zeroMult ρ.1)
        convert hb using 1 <;> first | rfl | ring
  have heq : (fun ρ => low ρ + high ρ) = f := by
    funext ρ
    dsimp [low, high]
    split_ifs <;> simp
  change Summable f
  rw [← heq]
  exact hl.add hh

theorem actual_Green_column_energy_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun ρ : CriticalZeros => (zeroMult ρ.1 : ℝ) *
      problemOneDirichletEnergy t (actualGreenOrdinate ρ)) := by
  apply Summable.of_nonneg_of_le (fun ρ =>
    mul_nonneg (Nat.cast_nonneg _) (problemOneDirichletEnergy_nonneg t _ ht.le))
    (fun ρ => ?_) (actual_Green_reciprocal_summable.mul_left
      (6 * t * (Real.exp (t / 2)) ^ 2))
  have he := problemOneColumnEnergySq_eq_dirichletEnergy t (actualGreenOrdinate ρ) ht
    (reflected_ordinate_denominator_ne_zero ρ.1 ρ.2)
  have hb := mul_le_mul_of_nonneg_left
    (problemOneColumnEnergySq_le t (actualGreenOrdinate ρ) ht (actualGreenOrdinate_strip ρ))
    (Nat.cast_nonneg (zeroMult ρ.1) : (0 : ℝ) ≤ zeroMult ρ.1)
  rw [he] at hb
  convert hb using 1 <;> first | rfl | ring


end WeilDefect.ConnesNative

theorem solution (t : ℝ) (ht : 0 < t) :
    Summable (fun ρ : ConnesRZFrontier.CriticalZeros => (ConnesRZ.zeroMult ρ.1 : ℝ) *
      WeilDefect.problemOneDirichletEnergy t (WeilDefect.ConnesNative.actualGreenOrdinate ρ)) :=
  WeilDefect.ConnesNative.actual_Green_column_energy_summable t ht
