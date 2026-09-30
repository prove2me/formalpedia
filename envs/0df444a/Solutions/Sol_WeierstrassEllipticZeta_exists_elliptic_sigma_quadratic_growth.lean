-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_elliptic_sigma_quadratic_growth
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T22:42:02.630323+00:00
-- url     : https://prove2.me/submissions/8d2810af-1069-4302-bd32-4f5b080dc3fa

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_differential_data
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.LinearCombination

noncomputable section
open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

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

/-- Commuting two translations forces symmetry of their real cross coefficients. -/
private lemma norm_periods_compatible (f : ℂ → ℂ) (ω₁ ω₂ η₁ η₂ : ℂ) (a₁ a₂ : ℝ)
    (h₁ : ∀ z, ‖f (z + ω₁)‖ = Real.exp (a₁ + (η₁ * z).re) * ‖f z‖)
    (h₂ : ∀ z, ‖f (z + ω₂)‖ = Real.exp (a₂ + (η₂ * z).re) * ‖f z‖)
    (u : ℂ) (hu : f u ≠ 0) : (η₁ * ω₂).re = (η₂ * ω₁).re := by
  have h : ‖f ((u + ω₁) + ω₂)‖ = ‖f ((u + ω₂) + ω₁)‖ := by
    congr 2
    ring
  rw [h₂ (u + ω₁), h₁ u, h₁ (u + ω₂), h₂ u,
    ← mul_assoc, ← mul_assoc] at h
  have he := Real.exp_injective (show
      Real.exp ((a₂ + (η₂ * (u + ω₁)).re) + (a₁ + (η₁ * u).re)) =
      Real.exp ((a₁ + (η₁ * (u + ω₂)).re) + (a₂ + (η₂ * u).re)) by
    simpa only [Real.exp_add] using (mul_right_cancel₀ (norm_ne_zero_iff.mpr hu) h))
  simp only [mul_add, Complex.add_re] at he
  linarith

private def latticeCoord (L : PeriodPair) (i : Fin 2) : ℂ →L[ℝ] ℝ :=
  (L.basis.coord i).toContinuousLinearMap

private lemma latticeCoord_repr (L : PeriodPair) (i : Fin 2) (z : ℂ) :
    latticeCoord L i z = (L.basis.repr z) i := rfl

private lemma latticeCoord_basis (L : PeriodPair) (i j : Fin 2) :
    latticeCoord L i (L.basis j) = if j = i then 1 else 0 := by
  rw [latticeCoord_repr, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

private lemma re_mul_coords (L : PeriodPair) (η z : ℂ) :
    (η * z).re = (η * L.ω₁).re * latticeCoord L 0 z +
      (η * L.ω₂).re * latticeCoord L 1 z := by
  have hz : (latticeCoord L 0 z : ℂ) * L.ω₁ +
      (latticeCoord L 1 z : ℂ) * L.ω₂ = z := by
    simpa only [Fin.sum_univ_two, PeriodPair.basis_zero, PeriodPair.basis_one,
      Complex.real_smul, latticeCoord_repr] using L.basis.sum_repr z
  conv_lhs => rw [← hz]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Every real quadratic polynomial in two linear coordinates has a quadratic norm bound. -/
private lemma quadratic_bound (x y : ℂ →L[ℝ] ℝ) (a b c d e : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      a * x z ^ 2 + b * (x z * y z) + c * y z ^ 2 + d * x z + e * y z ≤
        C * (1 + ‖z‖ ^ 2) := by
  let K := |a| + |b| + |c| + |d| + |e|
  let N := 1 + ‖x‖ ^ 2 + ‖y‖ ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨K * N, mul_nonneg hK hN, fun z => ?_⟩
  let T := 1 + x z ^ 2 + y z ^ 2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hx2 : |x z ^ 2| ≤ T := by rw [abs_of_nonneg (sq_nonneg _)]; dsimp [T]; nlinarith [sq_nonneg (y z)]
  have hy2 : |y z ^ 2| ≤ T := by rw [abs_of_nonneg (sq_nonneg _)]; dsimp [T]; nlinarith [sq_nonneg (x z)]
  have hxy : |x z * y z| ≤ T := by
    rw [abs_mul]
    dsimp [T]
    nlinarith [sq_nonneg (|x z| - |y z|), sq_abs (x z), sq_abs (y z)]
  have hx : |x z| ≤ T := by
    dsimp [T]
    nlinarith [sq_nonneg (|x z| - 1), sq_abs (x z), sq_nonneg (y z)]
  have hy : |y z| ≤ T := by
    dsimp [T]
    nlinarith [sq_nonneg (|y z| - 1), sq_abs (y z), sq_nonneg (x z)]
  have hm (p q : ℝ) (hq : |q| ≤ T) : p * q ≤ |p| * T :=
    (le_abs_self _).trans ((abs_mul p q).le.trans (mul_le_mul_of_nonneg_left hq (abs_nonneg p)))
  have hpoly : a * x z ^ 2 + b * (x z * y z) + c * y z ^ 2 + d * x z + e * y z ≤ K * T := by
    have h1 := hm a _ hx2
    have h2 := hm b _ hxy
    have h3 := hm c _ hy2
    have h4 := hm d _ hx
    have h5 := hm e _ hy
    dsimp [K]
    nlinarith
  have hxn : x z ^ 2 ≤ ‖x‖ ^ 2 * ‖z‖ ^ 2 := by
    have h := x.le_opNorm z
    rw [Real.norm_eq_abs] at h
    have hh := mul_self_le_mul_self (abs_nonneg (x z)) h
    nlinarith [sq_abs (x z)]
  have hyn : y z ^ 2 ≤ ‖y‖ ^ 2 * ‖z‖ ^ 2 := by
    have h := y.le_opNorm z
    rw [Real.norm_eq_abs] at h
    have hh := mul_self_le_mul_self (abs_nonneg (y z)) h
    nlinarith [sq_abs (y z)]
  have hTN : T ≤ N * (1 + ‖z‖ ^ 2) := by
    dsimp [T, N]
    nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖, sq_nonneg ‖z‖]
  calc
    _ ≤ K * T := hpoly
    _ ≤ K * (N * (1 + ‖z‖ ^ 2)) := mul_le_mul_of_nonneg_left hTN hK
    _ = _ := by ring

/-- A quadratic weight makes the norm periodic; compactness then supplies the bound. -/
private lemma periodic_norm_quadratic_growth (L : PeriodPair) (f : ℂ → ℂ)
    (hf : Continuous f) (η₁ η₂ : ℂ) (a₁ a₂ : ℝ)
    (h₁ : ∀ z, ‖f (z + L.ω₁)‖ = Real.exp (a₁ + (η₁ * z).re) * ‖f z‖)
    (h₂ : ∀ z, ‖f (z + L.ω₂)‖ = Real.exp (a₂ + (η₂ * z).re) * ‖f z‖)
    (hcompat : (η₁ * L.ω₂).re = (η₂ * L.ω₁).re) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ, ‖f z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)) := by
  let x := latticeCoord L 0
  let y := latticeCoord L 1
  have hx₁ : x L.ω₁ = 1 := by
    change latticeCoord L 0 L.ω₁ = 1
    rw [← L.basis_zero, latticeCoord_basis]
    norm_num
  have hx₂ : x L.ω₂ = 0 := by
    change latticeCoord L 0 L.ω₂ = 0
    rw [← L.basis_one, latticeCoord_basis]
    norm_num
  have hy₁ : y L.ω₁ = 0 := by
    change latticeCoord L 1 L.ω₁ = 0
    rw [← L.basis_zero, latticeCoord_basis]
    norm_num
  have hy₂ : y L.ω₂ = 1 := by
    change latticeCoord L 1 L.ω₂ = 1
    rw [← L.basis_one, latticeCoord_basis]
    norm_num
  let Q : ℂ → ℝ := fun z =>
    ((η₁ * L.ω₁).re / 2) * x z ^ 2 + (η₁ * L.ω₂).re * (x z * y z) +
    ((η₂ * L.ω₂).re / 2) * y z ^ 2 +
    (a₁ - (η₁ * L.ω₁).re / 2) * x z + (a₂ - (η₂ * L.ω₂).re / 2) * y z
  have hQ : Continuous Q := by fun_prop
  have hQ₁ (z : ℂ) : Q (z + L.ω₁) = Q z + a₁ + (η₁ * z).re := by
    dsimp only [Q]
    rw [map_add, map_add, hx₁, hy₁, re_mul_coords L η₁ z]
    change _ = _ + a₁ + ((η₁ * L.ω₁).re * x z + (η₁ * L.ω₂).re * y z)
    ring
  have hQ₂ (z : ℂ) : Q (z + L.ω₂) = Q z + a₂ + (η₂ * z).re := by
    dsimp only [Q]
    rw [map_add, map_add, hx₂, hy₂, re_mul_coords L η₂ z, ← hcompat]
    change _ = _ + a₂ + ((η₁ * L.ω₂).re * x z + (η₂ * L.ω₂).re * y z)
    ring
  let F : ℂ → ℝ := fun z => ‖f z‖ * Real.exp (-Q z)
  have hF : Continuous F := hf.norm.mul (Real.continuous_exp.comp hQ.neg)
  have hp₁ : Function.Periodic F L.ω₁ := by
    intro z
    dsimp only [F]
    rw [h₁ z, hQ₁ z]
    calc
      _ = ‖f z‖ * Real.exp ((a₁ + (η₁ * z).re) + -(Q z + a₁ + (η₁ * z).re)) := by
        rw [Real.exp_add (a₁ + (η₁ * z).re) (-(Q z + a₁ + (η₁ * z).re))]
        ring
      _ = _ := by congr 2; ring
  have hp₂ : Function.Periodic F L.ω₂ := by
    intro z
    dsimp only [F]
    rw [h₂ z, hQ₂ z]
    calc
      _ = ‖f z‖ * Real.exp ((a₂ + (η₂ * z).re) + -(Q z + a₂ + (η₂ * z).re)) := by
        rw [Real.exp_add (a₂ + (η₂ * z).re) (-(Q z + a₂ + (η₂ * z).re))]
        ring
      _ = _ := by congr 2; ring
  have hcompact : IsCompact (Set.range F) :=
    IsZLattice.isCompact_range_of_periodic L.lattice F hF (by
      intro z w hw
      obtain ⟨m, n, rfl⟩ := L.mem_lattice.mp hw
      simpa only [zsmul_eq_mul] using ((hp₁.zsmul m).add_period (hp₂.zsmul n)) z)
  obtain ⟨M, hM⟩ := hcompact.bddAbove
  obtain ⟨C, hC, hQC⟩ := quadratic_bound x y
    ((η₁ * L.ω₁).re / 2) (η₁ * L.ω₂).re ((η₂ * L.ω₂).re / 2)
    (a₁ - (η₁ * L.ω₁).re / 2) (a₂ - (η₂ * L.ω₂).re / 2)
  have hQC' (z : ℂ) : Q z ≤ C * (1 + ‖z‖ ^ 2) := hQC z
  refine ⟨|M| + C + 1, by positivity, fun z => ?_⟩
  have ht : 1 ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
  have hMexp : M ≤ Real.exp |M| :=
    (le_abs_self M).trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp |M|))
  have hFbound : F z ≤ Real.exp |M| := (hM (Set.mem_range_self z)).trans hMexp
  calc
    ‖f z‖ = F z * Real.exp (Q z) := by
      dsimp only [F]
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ Real.exp |M| * Real.exp (Q z) :=
      mul_le_mul_of_nonneg_right hFbound (Real.exp_pos _).le
    _ = Real.exp (|M| + Q z) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((|M| + C + 1) * (1 + ‖z‖ ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have h := hQC' z
      have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg M)
      nlinarith

theorem sigma_quadratic_growth_from_periods (L : PeriodPair)
    (S : EllipticSigmaDifferentialData L)
    (hder : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hperiod : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ, ‖S.sigma z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)) := by
  have hne := sigma_ne_zero L S hder
  obtain ⟨a₁, h₁⟩ := sigma_norm_add_period L S hne hperiod L.ω₁ L.ω₁_mem_lattice
  obtain ⟨a₂, h₂⟩ := sigma_norm_add_period L S hne hperiod L.ω₂ L.ω₂_mem_lattice
  exact periodic_norm_quadratic_growth L S.sigma S.entire.continuous
    (zetaQuasiPeriod L L.ω₁) (zetaQuasiPeriod L L.ω₂) a₁ a₂ h₁ h₂
    (norm_periods_compatible S.sigma L.ω₁ L.ω₂ _ _ a₁ a₂ h₁ h₂
      (L.ω₁ / 2) (hne _ L.ω₁_div_two_notMem_lattice))

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) :
    ∃ (D : EllipticSigmaDifferentialData L) (A : ℝ), 0 < A ∧
      ∀ z : ℂ, ‖D.sigma z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)) := by
  obtain ⟨D⟩ := exists_elliptic_sigma_differential_data L
  obtain ⟨A, hA, hbound⟩ := sigma_quadratic_growth_from_periods L D
    (hasDerivAt_weierstrassZeta L) (weierstrassZeta_add_period L)
  exact ⟨D, A, hA, hbound⟩
