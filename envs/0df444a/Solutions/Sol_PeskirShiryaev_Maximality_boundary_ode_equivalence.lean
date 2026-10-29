-- Prove2me | solution 1 for PeskirShiryaev.Maximality.boundary_ode_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:53:33.495014+00:00
-- url     : https://prove2.me/submissions/f6198e00-399a-4869-aef7-07cf167c8513

import Definitions.Def_PeskirShiryaev_Maximality_Boundary

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

open PeskirShiryaev.Maximality

section
variable (p : Coefficients)

noncomputable def s225mbW (y : ℝ) : ℝ := 2 * p.drift y / p.volatility y ^ 2

lemma s225mb_W_cont : Continuous (s225mbW p) := by
  unfold s225mbW
  refine Continuous.div (continuous_const.mul p.drift_continuous)
    (p.volatility_continuous.pow 2) (fun x => pow_ne_zero 2 (p.volatility_pos x).ne')

lemma s225mb_sd_eq : scaleDensity p = fun y => Real.exp (- ∫ z in (0 : ℝ)..y, s225mbW p z) := by
  funext y; rfl

lemma s225mb_sd_deriv (y : ℝ) :
    HasDerivAt (scaleDensity p) (scaleDensity p y * -s225mbW p y) y := by
  rw [s225mb_sd_eq]
  exact ((s225mb_W_cont p).integral_hasStrictDerivAt 0 y).hasDerivAt.neg.exp

lemma s225mb_sd_cont : Continuous (scaleDensity p) :=
  continuous_iff_continuousAt.mpr fun y => (s225mb_sd_deriv p y).continuousAt

lemma s225mb_sd_pos (y : ℝ) : 0 < scaleDensity p y := Real.exp_pos _

lemma s225mb_S_deriv (x : ℝ) : HasDerivAt (scale p) (scaleDensity p x) x :=
  ((s225mb_sd_cont p).integral_hasStrictDerivAt 0 x).hasDerivAt

lemma s225mb_S_cont : Continuous (scale p) :=
  continuous_iff_continuousAt.mpr fun y => (s225mb_S_deriv p y).continuousAt

lemma s225mb_m_cont : Continuous (speedDensity p) := by
  unfold speedDensity
  refine Continuous.div continuous_const ((s225mb_sd_cont p).mul
    (p.volatility_continuous.pow 2)) (fun x => ?_)
  exact mul_ne_zero (s225mb_sd_pos p x).ne' (pow_ne_zero 2 (p.volatility_pos x).ne')

noncomputable def s225mbK (y : ℝ) : ℝ := p.cost y * speedDensity p y

lemma s225mb_K_cont : Continuous (s225mbK p) :=
  p.cost_continuous.mul (s225mb_m_cont p)

lemma s225mb_S_lt {y s : ℝ} (h : y < s) : 0 < scale p s - scale p y := by
  unfold scale
  have hi : ∀ a b : ℝ, IntervalIntegrable (scaleDensity p) volume a b :=
    fun a b => (s225mb_sd_cont p).intervalIntegrable a b
  rw [intervalIntegral.integral_interval_sub_left (hi 0 s) (hi 0 y)]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (hi y s)
    (fun x _ => s225mb_sd_pos p x) h

/-- integralCandidate as S(x) K(x) - J(x). -/
lemma s225mb_IC_eq (g : ℝ → ℝ) (s : ℝ) :
    (fun x => integralCandidate p g x s) = fun x =>
      s + scale p x * (∫ y in g s..x, s225mbK p y) -
        ∫ y in g s..x, scale p y * s225mbK p y := by
  funext x
  unfold integralCandidate
  have h1 : (fun y => (scale p x - scale p y) * p.cost y * speedDensity p y) =
      fun y => scale p x * s225mbK p y - scale p y * s225mbK p y := by
    funext y; unfold s225mbK; ring
  rw [h1, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul]
  · ring
  · exact ((s225mb_K_cont p).const_smul (scale p x)).intervalIntegrable _ _
  · exact ((s225mb_S_cont p).mul (s225mb_K_cont p)).intervalIntegrable _ _

lemma s225mb_IC_hasDeriv (g : ℝ → ℝ) (s x : ℝ) :
    HasDerivAt (fun x => integralCandidate p g x s)
      (scaleDensity p x * ∫ y in g s..x, s225mbK p y) x := by
  rw [s225mb_IC_eq]
  have hK := ((s225mb_K_cont p).integral_hasStrictDerivAt (g s) x).hasDerivAt
  have hJ := (((s225mb_S_cont p).mul (s225mb_K_cont p)).integral_hasStrictDerivAt
    (g s) x).hasDerivAt
  have := ((hasDerivAt_const x s).add ((s225mb_S_deriv p x).mul hK)).sub hJ
  exact this.congr_deriv (by simp only [Pi.mul_apply]; ring)

lemma s225mb_IC_deriv (g : ℝ → ℝ) (s : ℝ) :
    deriv (fun x => integralCandidate p g x s) =
      fun x => scaleDensity p x * ∫ y in g s..x, s225mbK p y := by
  funext x; exact (s225mb_IC_hasDeriv p g s x).deriv

lemma s225mb_IC_deriv2 (g : ℝ → ℝ) (s x : ℝ) :
    deriv (deriv (fun x => integralCandidate p g x s)) x =
      scaleDensity p x * -s225mbW p x * (∫ y in g s..x, s225mbK p y) +
        scaleDensity p x * s225mbK p x := by
  rw [s225mb_IC_deriv]
  have hK := ((s225mb_K_cont p).integral_hasStrictDerivAt (g s) x).hasDerivAt
  exact ((s225mb_sd_deriv p x).mul hK).deriv

/-- derivative in the second argument (the running maximum). -/
lemma s225mb_IC_u (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (s u : ℝ) :
    HasDerivAt (fun u => integralCandidate p g s u)
      (1 - (scale p s - scale p (g u)) * p.cost (g u) * speedDensity p (g u) * deriv g u) u := by
  set h : ℝ → ℝ := fun y => (scale p s - scale p y) * p.cost y * speedDensity p y with hh
  have hcont : Continuous h :=
    ((continuous_const.sub (s225mb_S_cont p)).mul p.cost_continuous).mul (s225mb_m_cont p)
  have heq : (fun u => integralCandidate p g s u) = fun u => u - ∫ y in s..g u, h y := by
    funext u
    unfold integralCandidate
    rw [intervalIntegral.integral_symm]
    ring
  rw [heq]
  have hgd : HasDerivAt g (deriv g u) u :=
    ((hg.differentiable (by norm_num)) u).hasDerivAt
  have hI := ((hcont.integral_hasStrictDerivAt s (g u)).hasDerivAt).comp u hgd
  have := (hasDerivAt_id' u).sub hI
  exact this

end

theorem solution (p : Coefficients) (g : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) (hbelow : ∀ s, g s < s) :
    FreeBoundarySystem p g ↔ AdmissibleBoundary p g := by
  have hkey : ∀ s, (1 - (scale p s - scale p (g s)) * p.cost (g s) *
      speedDensity p (g s) * deriv g s = 0) ↔ deriv g s = odeRhs p s (g s) := by
    intro s
    have hS := s225mb_S_lt p (hbelow s)
    have hc := p.cost_pos (g s)
    have hsd := s225mb_sd_pos p (g s)
    have hv := p.volatility_pos (g s)
    unfold odeRhs speedDensity
    constructor
    · intro h
      field_simp
      field_simp at h
      linarith
    · intro h
      rw [h]
      field_simp
      ring
  have hderiv : ∀ s, HasDerivAt g (odeRhs p s (g s)) s ↔ deriv g s = odeRhs p s (g s) := by
    intro s
    constructor
    · intro h; exact h.deriv
    · intro h
      rw [← h]
      exact ((hg.differentiable (by norm_num)) s).hasDerivAt
  have hclause2 : ∀ s, HasDerivWithinAt (fun u => integralCandidate p g s u) 0 (Set.Ici s) s ↔
      deriv g s = odeRhs p s (g s) := by
    intro s
    rw [← hkey]
    have hD := s225mb_IC_u p g hg s s
    constructor
    · intro h
      exact (uniqueDiffWithinAt_Ici s).eq_deriv _ hD.hasDerivWithinAt h
    · intro h
      rw [← h]
      exact hD.hasDerivWithinAt
  constructor
  · rintro ⟨-, h2, -, -⟩
    exact ⟨hg, fun s => ⟨hbelow s, (hderiv s).mpr ((hclause2 s).mp (h2 s))⟩⟩
  · rintro ⟨-, h⟩
    refine ⟨?_, fun s => (hclause2 s).mpr ((h s).2.deriv), ?_, ?_⟩
    · intro s x _ _
      rw [s225mb_IC_deriv2, (s225mb_IC_hasDeriv p g s x).deriv]
      have hv := p.volatility_pos x
      have hsd := s225mb_sd_pos p x
      unfold s225mbW s225mbK speedDensity
      field_simp
      ring_nf
    · intro s
      unfold integralCandidate
      rw [intervalIntegral.integral_same, add_zero]
    · intro s
      have := s225mb_IC_hasDeriv p g s (g s)
      rw [intervalIntegral.integral_same, mul_zero] at this
      exact this.hasDerivWithinAt
