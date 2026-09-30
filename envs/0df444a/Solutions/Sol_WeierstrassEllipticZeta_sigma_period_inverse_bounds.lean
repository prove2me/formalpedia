-- Prove2me | solution 1 for WeierstrassEllipticZeta.sigma_period_inverse_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T23:02:41.499263+00:00
-- url     : https://prove2.me/submissions/a5300485-25f9-4e43-acff-4071d9929367

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.LinearCombination

noncomputable section
open Filter
open scoped Topology

open WeierstrassEllipticZeta

/-- The normalized differential solution has no zero away from the lattice. -/
private lemma sigma_ne_zero (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) : S.sigma z ≠ 0 := by
  intro hzero
  have hf := S.entire.analyticAt z
  have ha : AnalyticAt ℂ (weierstrassZeta L) z :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun w hw => (hzeta w hw).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl z hz
  have hfinite : analyticOrderAt S.sigma z ≠ ⊤ := by
    intro ho
    have heq : S.sigma = fun _ => 0 :=
      (show AnalyticOnNhd ℂ S.sigma Set.univ from fun w _ => S.entire.analyticAt w).eq_of_eventuallyEq
        (fun _ _ => analyticAt_const) (analyticOrderAt_eq_top.mp ho)
    have h0 := S.deriv_zero
    rw [heq] at h0
    have hbad := h0.unique (hasDerivAt_const (0 : ℂ) (0 : ℂ))
    norm_num at hbad
  have hderiv : deriv S.sigma =ᶠ[𝓝 z] S.sigma * weierstrassZeta L := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    simpa [mul_comm] using (S.hasDerivAt w hw).deriv
  have ho : analyticOrderAt (deriv S.sigma) z + 1 = analyticOrderAt S.sigma z := by
    simpa [hzero] using hf.analyticOrderAt_deriv_add_one
  rw [analyticOrderAt_congr hderiv, analyticOrderAt_mul hf ha] at ho
  have hle : analyticOrderAt S.sigma z + 1 ≤ analyticOrderAt S.sigma z := by
    calc
      _ ≤ (analyticOrderAt S.sigma z + analyticOrderAt (weierstrassZeta L) z) + 1 :=
        add_le_add (show analyticOrderAt S.sigma z ≤
          analyticOrderAt S.sigma z + analyticOrderAt (weierstrassZeta L) z from le_self_add) le_rfl
      _ = _ := ho
  exact (lt_irrefl _ ((ENat.add_one_le_iff hfinite).mp hle))

/-- Integrate the logarithmic derivative under a period translation, then extend globally. -/
private lemma sigma_norm_add_period (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (hzeta : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω)
    (ω : ℂ) (hω : ω ∈ L.lattice) :
    ∃ a : ℝ, ∀ z : ℂ, ‖S.sigma (z + ω)‖ =
      Real.exp (a + (zetaQuasiPeriod L ω * z).re) * ‖S.sigma z‖ := by
  let η := zetaQuasiPeriod L ω
  have hshift (z : ℂ) (hz : z ∉ L.lattice) : z + ω ∉ L.lattice := by
    intro h
    exact hz (by simpa using L.lattice.sub_mem h hω)
  have hd (z : ℂ) (hz : z ∉ L.lattice) :
      HasDerivAt (fun w => S.sigma (w + ω) / S.sigma w * Complex.exp (-η * w)) 0 z := by
    have h1 : HasDerivAt (fun w => S.sigma (w + ω))
        ((weierstrassZeta L z + η) * S.sigma (z + ω)) z := by
      simpa [hzeta ω z hω hz, η] using!
        (S.hasDerivAt (z + ω) (hshift z hz)).comp z ((hasDerivAt_id z).add_const ω)
    have h2 := ((hasDerivAt_id z).const_mul (-η)).cexp
    convert! ((h1.div (S.hasDerivAt z hz) (hne z hz)).mul h2) using 1
    simp only [Pi.div_apply, id_eq]
    field_simp
    ring
  obtain ⟨c, hc⟩ := L.isClosed_lattice.isOpen_compl.exists_is_const_of_deriv_eq_zero
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv)
  have heq (z : ℂ) (hz : z ∉ L.lattice) :
      S.sigma (z + ω) = c * Complex.exp (η * z) * S.sigma z := by
    have h := congrArg (fun w : ℂ => w * Complex.exp (η * z) * S.sigma z) (hc z hz)
    simpa [mul_assoc, ← Complex.exp_add, hne z hz] using h
  let u := L.ω₁ / 2
  have hu : u ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have hc0 : c ≠ 0 := by
    intro hc0
    have h := heq u hu
    simp only [hc0, zero_mul] at h
    exact hne (u + ω) (hshift u hu) h
  have hall : (fun z => S.sigma (z + ω)) =
      (fun z => c * Complex.exp (η * z) * S.sigma z) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (show AnalyticOnNhd ℂ (fun z => S.sigma (z + ω)) Set.univ from
        fun z _ => (S.entire.analyticAt (z + ω)).comp (f := fun w : ℂ => w + ω) (x := z)
          (analyticAt_id.add analyticAt_const))
      (show AnalyticOnNhd ℂ (fun z => c * Complex.exp (η * z) * S.sigma z) Set.univ from
        fun z _ => ((analyticAt_const.mul
          (analyticAt_const.mul analyticAt_id).cexp).mul (S.entire.analyticAt z)))
      (z₀ := u)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hu] with z hz
    exact heq z hz
  refine ⟨Real.log ‖c‖, fun z => ?_⟩
  rw [congrFun hall z, norm_mul, norm_mul, Complex.norm_exp, Real.exp_add,
    Real.exp_log (norm_pos_iff.mpr hc0)]

/-- Iterating an affine logarithmic increment gives an exact quadratic exponent. -/
private lemma norm_integer_translate (f : ℂ → ℂ) (u ω η : ℂ) (a : ℝ)
    (h : ∀ z, ‖f (z + ω)‖ = Real.exp (a + (η * z).re) * ‖f z‖) (n : ℤ) :
    ‖f (u + n * ω)‖ = ‖f u‖ * Real.exp
      ((a + (η * u).re) * n + (η * ω).re / 2 * n * (n - 1)) := by
  let Q : ℝ → ℝ := fun t => (a + (η * u).re) * t + (η * ω).re / 2 * t * (t - 1)
  have hQ (t : ℝ) : Q (t + 1) = Q t + a + (η * (u + (t : ℂ) * ω)).re := by
    dsimp [Q]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  let F : ℝ → ℝ := fun t => ‖f (u + (t : ℂ) * ω)‖ * Real.exp (-Q t)
  have hp : Function.Periodic F 1 := by
    intro t
    dsimp only [F]
    rw [show u + ((t + 1 : ℝ) : ℂ) * ω = (u + (t : ℂ) * ω) + ω by push_cast; ring,
      h, hQ]
    calc
      _ = ‖f (u + (t : ℂ) * ω)‖ * Real.exp
          ((a + (η * (u + (t : ℂ) * ω)).re) +
            -(Q t + a + (η * (u + (t : ℂ) * ω)).re)) := by
        rw [Real.exp_add (a + (η * (u + (t : ℂ) * ω)).re)
          (-(Q t + a + (η * (u + (t : ℂ) * ω)).re))]
        ring
      _ = _ := by congr 2; ring
  have he : F (n : ℝ) = F 0 := by simpa using hp.zsmul_eq n
  have hh := congrArg (fun r : ℝ => r * Real.exp (Q n)) he
  simpa [F, mul_assoc, ← Real.exp_add, Q] using hh

/-- Reciprocal powers on a fixed lattice progression have a quadratic exponent. -/
private lemma inverse_sigma_integer_translate (L : PeriodPair)
    (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (hperiod : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω)
    (u ω : ℂ) (hu : u ∉ L.lattice) (hω : ω ∈ L.lattice) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (k : ℕ),
      ‖S.sigma (u + n * ω) ^ k‖⁻¹ ≤
        Real.exp (C * k * (1 + (n : ℝ) ^ 2)) := by
  obtain ⟨a, ha⟩ := sigma_norm_add_period L S hne hperiod ω hω
  let α := a + (zetaQuasiPeriod L ω * u).re
  let β := (zetaQuasiPeriod L ω * ω).re / 2
  let b := Real.log ‖S.sigma u‖
  let C := |b| + |α| + 2 * |β| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun n k => ?_⟩
  have hn : ‖S.sigma (u + n * ω)‖ =
      Real.exp (b + α * n + β * n * (n - 1)) := by
    rw [norm_integer_translate S.sigma u ω (zetaQuasiPeriod L ω) a ha n]
    dsimp only [b, α, β]
    simp only [Real.exp_add, Real.exp_log (norm_pos_iff.mpr (hne u hu))]
    ring
  have hpoly : -(b + α * n + β * n * (n - 1)) ≤ C * (1 + (n : ℝ) ^ 2) := by
    have hnabs : |(n : ℝ)| ≤ 1 + (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (|(n : ℝ)| - 1), sq_abs (n : ℝ)]
    have h1 : -(α * n) ≤ |α| * (1 + (n : ℝ) ^ 2) := by
      calc
        _ ≤ |α * (n : ℝ)| := neg_le_abs _
        _ = |α| * |(n : ℝ)| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hnabs (abs_nonneg α)
    have h2 : |(n : ℝ) * (n - 1)| ≤ 2 * (1 + (n : ℝ) ^ 2) := by
      rw [show (n : ℝ) * (n - 1) = (n : ℝ) ^ 2 - n by ring]
      have h : |(n : ℝ) ^ 2 - n| ≤ |(n : ℝ) ^ 2| + |(n : ℝ)| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le ((n : ℝ) ^ 2) (n : ℝ)
      rw [abs_of_nonneg (sq_nonneg (n : ℝ))] at h
      nlinarith [sq_nonneg (n : ℝ)]
    have h3 : -(β * n * (n - 1)) ≤ 2 * |β| * (1 + (n : ℝ) ^ 2) := by
      calc
        _ ≤ |β * (n : ℝ) * (n - 1)| := neg_le_abs _
        _ = |β| * |(n : ℝ) * (n - 1)| := by rw [mul_assoc, abs_mul]
        _ ≤ |β| * (2 * (1 + (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg β)
        _ = _ := by ring
    have hb := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + (n : ℝ) ^ 2 by nlinarith [sq_nonneg (n : ℝ)]) (abs_nonneg b)
    have hb' := neg_le_abs b
    dsimp [C]
    nlinarith [sq_nonneg (n : ℝ)]
  rw [norm_pow, hn, ← Real.exp_nat_mul, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ (k : ℝ) by positivity)
  nlinarith

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z) :
    (∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0) ∧
      ∀ u ω : ℂ, u ∉ L.lattice → ω ∈ L.lattice →
        ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (k : ℕ),
          ‖D.sigma (u + n * ω) ^ k‖⁻¹ ≤
            Real.exp (C * k * (1 + (n : ℝ) ^ 2)) := by
  have hne := sigma_ne_zero L D h_zeta_deriv
  exact ⟨hne, fun u ω hu hω => inverse_sigma_integer_translate L D hne
    (weierstrassZeta_add_period L) u ω hu hω⟩
