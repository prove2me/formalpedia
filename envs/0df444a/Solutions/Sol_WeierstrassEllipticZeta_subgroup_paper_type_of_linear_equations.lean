-- Prove2me | solution 1 for WeierstrassEllipticZeta.subgroup_paper_type_of_linear_equations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T02:03:01.825317+00:00
-- url     : https://prove2.me/submissions/81ab0437-bf50-488d-9cb7-3f9bd0fd2465

import Definitions.Def_WeierstrassEllipticZeta_SubgroupLinearization
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_differential_data
import Theorems.Thm_WeierstrassEllipticZeta_sigma_addition_from_differential
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_group_geometry
import Theorems.Thm_WeierstrassEllipticZeta_projective_extension_group_with_regular_negation

-- Source: Solutions/EllipticPeriodQuasiperiodDeterminant.lean

noncomputable section
open Filter MvPolynomial WeierstrassEllipticZeta
open scoped Topology

/-- Integrate the logarithmic derivative under a period translation, then extend globally. -/
private lemma p2m_sigma_norm_translation (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
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

private lemma p2m_real_linear_is_real_mul (B : ℂ →ₗ[ℝ] ℝ) :
    ∃ b : ℂ, ∀ z : ℂ, (b * z).re = B z := by
  refine ⟨(B 1 : ℂ) - (B Complex.I : ℂ) * Complex.I, fun z => ?_⟩
  have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by
    simpa only [Complex.real_smul, mul_one] using Complex.re_add_im z
  have hB : B z = z.re * B 1 + z.im * B Complex.I := by
    conv_lhs => rw [← hz]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hB]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, sub_zero]
  ring

theorem WeierstrassEllipticZeta.period_quasiperiod_determinant_ne_zero (L : PeriodPair) :
    L.ω₁ * zetaQuasiPeriod L L.ω₂ - L.ω₂ * zetaQuasiPeriod L L.ω₁ ≠ 0 := by
  intro hdet
  have hω₁ : L.ω₁ ≠ 0 := by
    simpa using L.indep.ne_zero (0 : Fin 2)
  let a := zetaQuasiPeriod L L.ω₁ / L.ω₁
  have hη₁ : zetaQuasiPeriod L L.ω₁ = a * L.ω₁ := by
    dsimp [a]
    rw [div_mul_cancel₀ _ hω₁]
  have hη₂ : zetaQuasiPeriod L L.ω₂ = a * L.ω₂ := by
    apply mul_left_cancel₀ hω₁
    calc
      _ = L.ω₂ * zetaQuasiPeriod L L.ω₁ := sub_eq_zero.mp hdet
      _ = _ := by rw [hη₁]; ring
  obtain ⟨S⟩ := exists_elliptic_sigma_differential_data L
  have hne := (sigma_addition_from_differential L S (hasDerivAt_weierstrassZeta L)
    (zeta_addition_formula L)).1
  obtain ⟨r₁, hr₁⟩ := p2m_sigma_norm_translation L S hne
    (weierstrassZeta_add_period L) L.ω₁ L.ω₁_mem_lattice
  obtain ⟨r₂, hr₂⟩ := p2m_sigma_norm_translation L S hne
    (weierstrassZeta_add_period L) L.ω₂ L.ω₂_mem_lattice
  let B : ℂ →ₗ[ℝ] ℝ :=
    (r₁ - (a * L.ω₁ ^ 2 / 2).re) • L.basis.coord 0 +
    (r₂ - (a * L.ω₂ ^ 2 / 2).re) • L.basis.coord 1
  have hB₁ : B L.ω₁ = r₁ - (a * L.ω₁ ^ 2 / 2).re := by
    rw [← L.basis_zero]
    simp only [B, LinearMap.add_apply, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self]
    norm_num
  have hB₂ : B L.ω₂ = r₂ - (a * L.ω₂ ^ 2 / 2).re := by
    rw [← L.basis_one]
    simp only [B, LinearMap.add_apply, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self]
    norm_num
  obtain ⟨b, hb⟩ := p2m_real_linear_is_real_mul B
  let Q : ℂ → ℂ := fun z => a * z ^ 2 / 2 + b * z
  let F : ℂ → ℂ := fun z => Complex.exp (-Q z) * S.sigma z
  have hF : Differentiable ℂ F := by
    have hS := S.entire
    dsimp only [F, Q]
    fun_prop
  have hQ (ω η : ℂ) (r : ℝ) (hη : η = a * ω)
      (hB : B ω = r - (a * ω ^ 2 / 2).re) (z : ℂ) :
      (Q (z + ω)).re = (Q z).re + r + (η * z).re := by
    have heq : Q (z + ω) = Q z + η * z + (a * ω ^ 2 / 2 + b * ω) := by
      rw [hη]
      dsimp only [Q]
      ring
    rw [heq]
    simp only [Complex.add_re, hb, hB]
    ring
  have hp (ω η : ℂ) (r : ℝ)
      (hr : ∀ z : ℂ, ‖S.sigma (z + ω)‖ = Real.exp (r + (η * z).re) * ‖S.sigma z‖)
      (hη : η = a * ω) (hB : B ω = r - (a * ω ^ 2 / 2).re) :
      Function.Periodic (fun z => ‖F z‖) ω := by
    intro z
    dsimp only [F]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
      Complex.neg_re, Complex.neg_re, hr, hQ ω η r hη hB z, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hp₁ := hp L.ω₁ _ r₁ hr₁ hη₁ hB₁
  have hp₂ := hp L.ω₂ _ r₂ hr₂ hη₂ hB₂
  have hcompact : IsCompact (Set.range (fun z => ‖F z‖)) :=
    IsZLattice.isCompact_range_of_periodic L.lattice _ hF.continuous.norm (by
      intro z w hw
      obtain ⟨m, n, rfl⟩ := L.mem_lattice.mp hw
      simpa only [zsmul_eq_mul] using ((hp₁.zsmul m).add_period (hp₂.zsmul n)) z)
  obtain ⟨M, hM⟩ := hcompact.bddAbove
  have hbounded : Bornology.IsBounded (Set.range F) :=
    isBounded_iff_forall_norm_le.mpr ⟨M, by
      rintro _ ⟨z, rfl⟩
      exact hM (Set.mem_range_self z)⟩
  have hzero := hF.apply_eq_apply_of_bounded hbounded (L.ω₁ / 2) 0
  have hnonzero : F (L.ω₁ / 2) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (hne _ L.ω₁_div_two_notMem_lattice)
  apply hnonzero
  simpa [F, Q, S.zero] using hzero

end

-- Source: Solutions/EllipticPolynomialSaturation.lean

noncomputable section
open MvPolynomial
open WeierstrassEllipticZeta TranscendenceTheory
open scoped Classical

namespace WeierstrassEllipticZeta

private lemma nat_period_mem (L : PeriodPair) (ω : ℂ)
    (hω : ω ∈ L.lattice) (n : ℕ) : (n : ℂ) * ω ∈ L.lattice := by
  simpa [nsmul_eq_mul] using L.lattice.nsmul_mem hω n

private lemma regular_add_period (L : PeriodPair) (z ω : ℂ)
    (hz : z ∉ L.lattice) (hω : ω ∈ L.lattice) : z + ω ∉ L.lattice := by
  intro h
  exact hz (by simpa only [add_sub_cancel_right] using L.lattice.sub_mem h hω)

private lemma zeta_add_nat_period (L : PeriodPair) (ω : ℂ)
    (hω : ω ∈ L.lattice) (z : ℂ) (hz : z ∉ L.lattice) (n : ℕ) :
    weierstrassZeta L (z + (n : ℂ) * ω) =
      weierstrassZeta L z + (n : ℂ) * zetaQuasiPeriod L ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show z + ((n + 1 : ℕ) : ℂ) * ω = (z + (n : ℂ) * ω) + ω by
      push_cast; ring]
    rw [weierstrassZeta_add_period L ω _ hω
      (regular_add_period L z _ hz (nat_period_mem L ω hω n)), ih]
    push_cast
    ring

/-- A nonvertical analytic line saturates both additive coordinates in every regular
elliptic fibre. The derivative coordinate is retained, so no false independence of
`wp` and `wp'` is asserted. -/
theorem linear_direction_polynomial_saturation (L : PeriodPair)
    (α β : ℂ) (hα : α ≠ 0) (P : MvPolynomial (Fin 4) ℂ)
    (hP : ∀ z : ℂ, z ∉ L.lattice →
      eval ![α * z, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z + β * z] P = 0) :
    ∀ z : ℂ, z ∉ L.lattice → ∀ t u : ℂ,
      eval ![t, L.weierstrassP z, L.derivWeierstrassP z, u] P = 0 := by
  classical
  intro z hz t u
  let a₁ := α * L.ω₁
  let a₂ := α * L.ω₂
  let b₁ := zetaQuasiPeriod L L.ω₁ + β * L.ω₁
  let b₂ := zetaQuasiPeriod L L.ω₂ + β * L.ω₂
  let d := a₁ * b₂ - a₂ * b₁
  have hd : d ≠ 0 := by
    have heq : d = α * (L.ω₁ * zetaQuasiPeriod L L.ω₂ -
        L.ω₂ * zetaQuasiPeriod L L.ω₁) := by
      dsimp [d, a₁, a₂, b₁, b₂]
      ring
    rw [heq]
    exact mul_ne_zero hα (period_quasiperiod_determinant_ne_zero L)
  let f : Fin 4 → MvPolynomial (Fin 2) ℂ :=
    ![C (α * z) + C a₁ * X 0 + C a₂ * X 1,
      C (L.weierstrassP z), C (L.derivWeierstrassP z),
      C (weierstrassZeta L z + β * z) + C b₁ * X 0 + C b₂ * X 1]
  let Q : MvPolynomial (Fin 2) ℂ := eval₂ C f P
  have hQeval (a b : ℂ) : eval ![a, b] Q =
      eval ![α * z + a * a₁ + b * a₂, L.weierstrassP z,
        L.derivWeierstrassP z, weierstrassZeta L z + β * z + a * b₁ + b * b₂] P := by
    dsimp only [Q]
    rw [← eval_assoc]
    apply congrArg (fun v : Fin 4 → ℂ => eval v P)
    funext i
    fin_cases i <;> simp [f, mul_comm]
  have hQ : Q = 0 := by
    apply funext_set (fun _ : Fin 2 => Set.range (fun n : ℕ => (n : ℂ)))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro v hv
    obtain ⟨a, ha⟩ := hv 0 (Set.mem_univ _)
    obtain ⟨b, hb⟩ := hv 1 (Set.mem_univ _)
    have hvval : v = ![(a : ℂ), (b : ℂ)] := by
      funext i
      fin_cases i
      · exact ha.symm
      · exact hb.symm
    rw [hvval, hQeval, map_zero]
    have haL := nat_period_mem L L.ω₁ L.ω₁_mem_lattice a
    have hbL := nat_period_mem L L.ω₂ L.ω₂_mem_lattice b
    have hza := regular_add_period L z _ hz haL
    have hzab := regular_add_period L _ _ hza hbL
    have hwp : L.weierstrassP (z + (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) =
        L.weierstrassP z := by
      rw [L.weierstrassP_add_coe _ ⟨_, hbL⟩, L.weierstrassP_add_coe _ ⟨_, haL⟩]
    have hwpp : L.derivWeierstrassP (z + (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) =
        L.derivWeierstrassP z := by
      rw [L.derivWeierstrassP_add_coe _ ⟨_, hbL⟩, L.derivWeierstrassP_add_coe _ ⟨_, haL⟩]
    have hζ := zeta_add_nat_period L L.ω₂ L.ω₂_mem_lattice _ hza b
    rw [zeta_add_nat_period L L.ω₁ L.ω₁_mem_lattice z hz a] at hζ
    have he := hP _ hzab
    rw [hwp, hwpp, hζ] at he
    convert he using 1
    apply congrArg (fun w : Fin 4 → ℂ => eval w P)
    funext i
    fin_cases i <;> simp [a₁, a₂, b₁, b₂, mul_add, add_mul] <;> ring
  let a := ((t - α * z) * b₂ - a₂ * (u - (weierstrassZeta L z + β * z))) / d
  let b := (a₁ * (u - (weierstrassZeta L z + β * z)) - (t - α * z) * b₁) / d
  have ht : α * z + a * a₁ + b * a₂ = t := by
    calc
      _ = α * z + ((t - α * z) * d) / d := by dsimp [a, b, d]; ring
      _ = t := by rw [mul_div_cancel_right₀ _ hd]; ring
  have hu : weierstrassZeta L z + β * z + a * b₁ + b * b₂ = u := by
    calc
      _ = weierstrassZeta L z + β * z +
          ((u - (weierstrassZeta L z + β * z)) * d) / d := by
        dsimp [a, b, d]; ring
      _ = u := by rw [mul_div_cancel_right₀ _ hd]; ring
  have hh := hQeval a b
  rw [hQ, map_zero, ht, hu] at hh
  exact hh.symm


end WeierstrassEllipticZeta
end

-- Source: Solutions/WeierstrassLinearDirectionSaturation.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open MvPolynomial Filter
open scoped Topology
namespace WeierstrassEllipticZeta

/-- A line with nonzero elliptic coordinate fills the extension factor in its
Zariski closure. Its first additive coordinate may be zero. -/
theorem linear_direction_polynomial_saturation_with_zero
    (L : PeriodPair) (α β : ℂ) (P : MvPolynomial (Fin 4) ℂ)
    (hP : ∀ z : ℂ, z ∉ L.lattice →
      eval ![α * z, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z + β * z] P = 0) :
    ∀ z : ℂ, z ∉ L.lattice → ∀ t u : ℂ,
      eval ![α * t, L.weierstrassP z, L.derivWeierstrassP z, u] P = 0 := by
  let R : MvPolynomial (Fin 4) ℂ := aeval ![C α * X 0, X 1, X 2, X 3] P
  have hR (t x y u : ℂ) : eval ![t, x, y, u] R = eval ![α * t, x, y, u] P := by
    change (aeval ![t, x, y, u]) ((aeval ![C α * X 0, X 1, X 2, X 3]) P) = _
    rw [comp_aeval_apply]
    apply congrArg (fun w : Fin 4 → ℂ => eval w P)
    funext i
    fin_cases i <;> simp
  have hline : ∀ z : ℂ, z ∉ L.lattice →
      eval ![1 * z, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z + β * z] R = 0 := by
    intro z hz
    simpa only [one_mul, hR] using hP z hz
  intro z hz t u
  rw [← hR]
  exact linear_direction_polynomial_saturation L 1 β one_ne_zero R hline z hz t u

private theorem normalize_eval (Q : MvPolynomial (Fin 7) ℂ) (t x y u : ℂ) :
    eval ![t, x, y, u] (extensionChartNormalize 0 Q) =
      eval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] Q := by
  change (aeval ![t, x, y, u]) ((aeval (extensionChartSubstitution 0)) Q) = _
  rw [comp_aeval_apply]
  apply congrArg (fun v : Fin 7 → ℂ => eval v Q)
  funext i
  fin_cases i <;> simp [extensionChartSubstitution]

private theorem block_scale (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (v : Fin 7 → ℂ) (r : ℂ) :
    eval ![v 0, v 1, r * v 2, r * v 3, r * v 4, r * v 5, r * v 6] Q =
      r ^ n * eval v Q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← hQ d hd]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

variable (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)

include hS_value in
private theorem regular_eval
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (t z u : ℂ) (hz : z ∉ L.lattice) :
    eval ![1, t, S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z,
      S 4 z + u * S 2 z] Q =
      (D.sigma z ^ 3) ^ n * eval
        ![t, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z + u]
        (extensionChartNormalize 0 Q) := by
  rw [normalize_eval, ← block_scale Q n hQ _ (D.sigma z ^ 3)]
  apply congrArg (fun v : Fin 7 → ℂ => eval v Q)
  funext i
  fin_cases i <;> simp [hS_value z hz] <;> ring

include hS hS_value hS_ne in
/-- Actual entire homogeneous coordinates, including lattice fibres: a section
vanishing on `exp(α z,z,β z)` vanishes on `exp(α t,z,u)` for every `t,z,u`.
For `α = 0` this is the whole extension factor; for `α ≠ 0` it is the whole group. -/
theorem projective_linear_direction_saturation
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (α β : ℂ)
    (hline : ∀ z : ℂ,
      eval ![1, α * z, S 0 z, S 1 z, S 2 z,
        S 3 z + (β * z) * S 0 z, S 4 z + (β * z) * S 2 z] Q = 0) :
    ∀ t z u : ℂ,
      eval ![1, α * t, S 0 z, S 1 z, S 2 z,
        S 3 z + u * S 0 z, S 4 z + u * S 2 z] Q = 0 := by
  have hregular : ∀ z : ℂ, z ∉ L.lattice →
      eval ![α * z, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z + β * z] (extensionChartNormalize 0 Q) = 0 := by
    intro z hz
    have hsig : D.sigma z ≠ 0 := by
      intro hs
      obtain ⟨j, hj⟩ := hS_ne z
      exact hj (by simp [hS_value z hz, hs])
    have hh := hline z
    rw [regular_eval L D S hS_value Q n hQ (α * z) z (β * z) hz] at hh
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero n (pow_ne_zero 3 hsig))
  have hsaturated := linear_direction_polynomial_saturation_with_zero L α β
    (extensionChartNormalize 0 Q) hregular
  intro t z u
  have ha : AnalyticOnNhd ℂ (fun w : ℂ =>
      eval ![1, α * t, S 0 w, S 1 w, S 2 w, S 3 w + u * S 0 w,
        S 4 w + u * S 2 w] Q) Set.univ := by
    intro w _
    apply AnalyticAt.aeval_mvPolynomial
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_const
    · exact hS 0 w trivial
    · exact hS 1 w trivial
    · exact hS 2 w trivial
    · exact (hS 3 w trivial).add (analyticAt_const.mul (hS 0 w trivial))
    · exact (hS 4 w trivial).add (analyticAt_const.mul (hS 2 w trivial))
  have hall := AnalyticOnNhd.eq_of_eventuallyEq ha
    (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
    (z₀ := L.ω₁ / 2) (by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds L.ω₁_div_two_notMem_lattice]
        with w hw
      rw [regular_eval L D S hS_value Q n hQ (α * t) w u hw,
        hsaturated w hw t (weierstrassZeta L w + u), mul_zero]
      rfl)
  exact congrFun hall z

end WeierstrassEllipticZeta
end

-- Source: Solutions/PhilipponProjectiveGeometry.lean

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem vanishingIdeal_antitone {S T : Set M.Point} (h : S ⊆ T) :
    M.vanishingIdeal T ≤ M.vanishingIdeal S := by
  apply Ideal.span_mono
  rintro P ⟨hP, hz⟩
  exact ⟨hP, fun x hx => hz x (h hx)⟩

theorem isClosed_zeroLocus_vanishingIdeal (S : Set M.Point) :
    @IsClosed _ M.zariskiTopology (M.zeroLocus (M.vanishingIdeal S)) := by
  letI := M.zariskiTopology
  have hset : M.zeroLocus (M.vanishingIdeal S) =
      ⋂ P : {P : M.CoordinateRing // (∃ D, M.IsHomogeneous P D) ∧
        ∀ x ∈ S, M.eval P x = 0}, {x | M.eval P.val x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, zeroLocus]
    constructor
    · intro hx P
      exact hx P (Ideal.subset_span P.property)
    · intro hx P hP
      have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
        apply Ideal.span_le.mpr
        intro Q hQ
        exact hx ⟨Q, hQ⟩
      exact hle hP
  rw [hset]
  apply isClosed_iInter
  intro P
  obtain ⟨D, hD⟩ := P.property.1
  exact M.isClosed_zero P.val D hD

/-- The chosen-representative ideal agrees with Zariski closure. -/
theorem zeroLocus_vanishingIdeal_eq_closure (S : Set M.Point) :
    M.zeroLocus (M.vanishingIdeal S) = @closure _ M.zariskiTopology S := by
  letI := M.zariskiTopology
  apply Set.Subset.antisymm
  · intro x hx
    apply M.isTopologicalBasis_basic.mem_closure_iff.mpr
    rintro U ⟨P, D, hP, rfl⟩ hxU
    by_contra hn
    have hPS : ∀ y ∈ S, M.eval P y = 0 := by
      intro y hy
      by_contra hp
      exact hn ⟨y, hp, hy⟩
    exact hxU (hx P (Ideal.subset_span ⟨⟨D, hP⟩, hPS⟩))
  · apply closure_minimal
    · intro x hx P hP
      exact M.eval_eq_zero_of_mem_vanishingIdeal hP hx
    · exact M.isClosed_zeroLocus_vanishingIdeal S

end MultiProjectiveSpace

theorem singleBlock_isHomogeneous {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    (projectiveSpace K N).IsHomogeneous
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => d) := by
  classical
  intro a ha i
  have h := hP.rename_isHomogeneous (f := fun j => (⟨(0 : Fin 1), j⟩ :
    (projectiveSpace K N).Variable)) (MvPolynomial.mem_support_iff.mp ha)
  change Finsupp.weight (1 : (projectiveSpace K N).Variable → ℕ) a = d at h
  rw [Finsupp.weight_eq_sum] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma] at h
  change (∑ x : Fin 1, ∑ y : Fin (N + 1), a ⟨x, y⟩) = d at h
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change (∑ j : Fin (N + 1), a ⟨(0 : Fin 1), j⟩) = d
  exact (Fin.sum_univ_one _).symm.trans h

theorem projective_isClosed_zero {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    @IsClosed _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | MvPolynomial.eval p.rep P = 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isClosed_zero _ _
    (singleBlock_isHomogeneous hP)).preimage hcont
  convert h using 1
  ext p
  change MvPolynomial.eval p.rep P = 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => p) = 0
  simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_rename]
  rfl

theorem projective_isOpen_coordinate {K : Type*} [Field K] {N : ℕ}
    (j : Fin (N + 1)) :
    @IsOpen _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | p.rep j ≠ 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isOpen_basic _ _
    (singleBlock_isHomogeneous (MvPolynomial.isHomogeneous_X K j))).preimage
      hcont
  convert h using 1
  ext p
  change p.rep j ≠ 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) (MvPolynomial.X j)) (fun _ => p) ≠ 0
  simp [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate]

theorem projective_regular_of_homogeneous
    {K X : Type u} [Field K] {N N' d : ℕ}
    (e : X → Projectivization K (Fin (N + 1) → K))
    (f : X → Projectivization K (Fin (N' + 1) → K))
    (P : Fin (N' + 1) → MvPolynomial (Fin (N + 1)) K)
    (hP : ∀ j, (P j).IsHomogeneous d)
    (hf : ∀ x, ∃ h : (fun j => MvPolynomial.eval (e x).rep (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval (e x).rep (P j)) h = f x) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K N) (projectiveSpace K N')
      (fun x => fun _ => e x) (fun x => fun _ => f x) := by
  letI := (projectiveSpace K N).zariskiTopology
  intro x b
  let Q : Fin (N' + 1) → (projectiveSpace K N).CoordinateRing :=
    fun j => MvPolynomial.rename (fun k => ⟨(0 : Fin 1), k⟩) (P j)
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => d,
    Q,
    (fun j => singleBlock_isHomogeneous (hP j)), ?_⟩
  intro y _
  have heq : (fun j => (projectiveSpace K N).eval (Q j) (fun _ => e y)) =
      (fun j => MvPolynomial.eval (e y).rep (P j)) := by
    ext j
    change MvPolynomial.eval _ (MvPolynomial.rename _ (P j)) = _
    rw [MvPolynomial.eval_rename]
    rfl
  obtain ⟨hne, hmk⟩ := hf y
  change ∃ h : (fun j : Fin (N' + 1) =>
      (projectiveSpace K N).eval (Q j) (fun _ => e y)) ≠ 0,
    Projectivization.mk K
      (fun j : Fin (N' + 1) => (projectiveSpace K N).eval (Q j) (fun _ => e y)) h = f y
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hne
  · simpa only [heq] using hmk

end PhilipponMultiplicity

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

theorem projective_extension_locallyClosed (g₂ g₃ : ℂ) :
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p _ => p) (projectiveSpace ℂ 4).zariskiTopology)
      {p : Projectivization ℂ (Fin 5 → ℂ) |
        MvPolynomial.eval p.rep extensionQuadric = 0 ∧
        MvPolynomial.eval p.rep (extensionCubic g₂ g₃) = 0 ∧
        (p.rep 0 ≠ 0 ∨ p.rep 2 ≠ 0)} := by
  letI := TopologicalSpace.induced (fun (p : Projectivization ℂ (Fin 5 → ℂ)) =>
    (fun _ => p : (projectiveSpace ℂ 4).Point)) (projectiveSpace ℂ 4).zariskiTopology
  have hq : extensionQuadric.IsHomogeneous 2 := by
    exact ((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X ℂ 4)).sub
      ((MvPolynomial.isHomogeneous_X ℂ 2).mul (MvPolynomial.isHomogeneous_X ℂ 3)) |>.sub
        (MvPolynomial.isHomogeneous_C_mul_X_pow 2 1 2)
  have hc : (extensionCubic g₂ g₃).IsHomogeneous 3 := by
    exact (((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X_pow 2 2)).sub
      (MvPolynomial.isHomogeneous_C_mul_X_pow 4 1 3)).add
        ((MvPolynomial.isHomogeneous_C_mul_X_pow g₂ 0 2).mul
          (MvPolynomial.isHomogeneous_X ℂ 1)) |>.add
        (MvPolynomial.isHomogeneous_C_mul_X_pow g₃ 0 3)
  convert
    ((projective_isClosed_zero hq).inter (projective_isClosed_zero hc)).isLocallyClosed.inter
      ((projective_isOpen_coordinate (K := ℂ) (0 : Fin 5)).union
        (projective_isOpen_coordinate (K := ℂ) (2 : Fin 5))).isLocallyClosed using 1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, and_assoc]

theorem projective_extension_fiber_action_regular (g₂ g₃ u : ℂ)
    (F : ProjectiveExtensionFiberModel g₂ g₃) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun p : ProjectiveExtensionChartLocus g₂ g₃ => fun _ => extensionProjectivePoint p)
      (fun p => fun _ => extensionProjectivePoint (F.action u p)) := by
  let P : Fin 5 → MvPolynomial (Fin 5) ℂ :=
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
      MvPolynomial.X 3 + MvPolynomial.C u * MvPolynomial.X 0,
      MvPolynomial.X 4 + MvPolynomial.C u * MvPolynomial.X 2]
  apply projective_regular_of_homogeneous _ _ P (d := 1)
  · intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · exact MvPolynomial.isHomogeneous_X ℂ 1
    · exact MvPolynomial.isHomogeneous_X ℂ 2
    · exact (MvPolynomial.isHomogeneous_X ℂ 3).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 0))
    · exact (MvPolynomial.isHomogeneous_X ℂ 4).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 2))
  · intro p
    have heq : (fun j => MvPolynomial.eval (extensionProjectivePoint p).rep (P j)) =
        extensionFiberShear u (extensionProjectivePoint p).rep := by
      ext j
      fin_cases j <;> simp [P, extensionFiberShear]
    obtain ⟨h, hh⟩ := F.action_coords u p
    exact ⟨by simpa only [heq] using h, by simpa only [heq] using hh.symm⟩

end WeierstrassEllipticZeta
end

-- Source: Solutions/PhilipponDensityCriterion.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.EmbeddedGroupProduct

/-- Density in the actual induced multiprojective topology is equivalent to
having no additional homogeneous relations on the proposed dense subset. -/
theorem dense_iff_homogeneous_vanishing {K : Type*} [Field K]
    (G : EmbeddedGroupProduct K) (S : Set G.Point) :
    @Dense _ G.zariskiTopology S ↔
      ∀ (P : G.CoordinateRing) (D : G.FactorIndex → ℕ), G.ambient.IsHomogeneous P D →
        (∀ x ∈ S, G.ambient.eval P (G.embedding x) = 0) →
        ∀ x : G.Point, G.ambient.eval P (G.embedding x) = 0 := by
  letI := G.ambient.zariskiTopology
  letI := G.zariskiTopology
  have hcl : @closure _ G.zariskiTopology S =
      G.embedding ⁻¹' G.ambient.zeroLocus (G.vanishingIdeal S) := by
    ext x
    rw [zariskiTopology, closure_induced]
    rw [← G.ambient.zeroLocus_vanishingIdeal_eq_closure]
    rfl
  rw [dense_iff_closure_eq, hcl, Set.eq_univ_iff_forall]
  constructor
  · intro h P D hP hzero x
    apply h x P
    apply Ideal.subset_span
    refine ⟨⟨D, hP⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hzero y hy
  · intro h x P hP
    have hle : G.vanishingIdeal S ≤ RingHom.ker
        (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
      apply Ideal.span_le.mpr
      rintro Q ⟨⟨D, hQ⟩, hzero⟩
      exact h Q D hQ (fun y hy => hzero _ ⟨y, hy, rfl⟩) x
    exact hle hP

end PhilipponMultiplicity.EmbeddedGroupProduct

end

-- Source: Solutions/PhilipponClosedLocusSeparation.lean

set_option autoImplicit false
noncomputable section
namespace PhilipponMultiplicity.EmbeddedGroupProduct

/-- A proper closed locus has a homogeneous equation that fails somewhere on
every Zariski-dense subset. -/
theorem exists_homogeneous_separator {K : Type*} [Field K]
    (G : EmbeddedGroupProduct K) (S C : Set G.Point)
    (hS : @Dense _ G.zariskiTopology S) (hC : @IsClosed _ G.zariskiTopology C)
    (hproper : C ≠ Set.univ) :
    ∃ P : G.CoordinateRing, ∃ D : G.FactorIndex → ℕ,
      G.ambient.IsHomogeneous P D ∧
      (∀ x ∈ C, G.ambient.eval P (G.embedding x) = 0) ∧
      ∃ x ∈ S, G.ambient.eval P (G.embedding x) ≠ 0 := by
  classical
  letI := G.zariskiTopology
  by_contra! hn
  have hCdense : Dense C := (G.dense_iff_homogeneous_vanishing C).mpr (by
    intro P D hP hzero x
    exact (G.dense_iff_homogeneous_vanishing S).mp hS P D hP (hn P D hP hzero) x)
  exact hproper (hC.closure_eq.symm.trans hCdense.closure_eq)

end PhilipponMultiplicity.EmbeddedGroupProduct
end

-- Source: Solutions/PhilipponHomogeneousOperations.lean

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.nat_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : ℕ) : M.IsHomogeneous (c * P) D := by
  simpa only [map_natCast] using hP.C_mul M (c : K)

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

end PhilipponMultiplicity.MultiProjectiveSpace
end

-- Source: Solutions/WeierstrassModelHomogeneous.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity

namespace PhilipponMultiplicity.MultiProjectiveSpace
theorem IsHomogeneous.degree_unique {K : Type*} [Field K]
    {M : MultiProjectiveSpace K} {P : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hD : M.IsHomogeneous P D) (hE : M.IsHomogeneous P E) (hne : P ≠ 0) : D = E := by
  obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr (by simpa using hne : P.support ≠ ∅)
  funext i
  exact (hD d hd i).symm.trans (hE d hd i)
end PhilipponMultiplicity.MultiProjectiveSpace

namespace WeierstrassEllipticZeta.PhilipponApplication.Model
variable {S : Fin 5 → ℂ → ℂ} (M : Model S)

/-- The stipulated bihomogeneity forces the variable equivalence to preserve
the additive block and the extension block individually. -/
theorem variableEquiv_block (j : Fin 7) :
    (M.variableEquiv j).1 = if j.val < 2 then (0 : Fin 2) else 1 := by
  classical
  have hQ : Bihomogeneous (X j) (if j.val < 2 then 1 else 0)
      (if j.val < 2 then 0 else 1) := by
    intro d hd
    simp only [support_X, Finset.mem_singleton] at hd
    subst d
    fin_cases j <;> simp
  have hh := M.homogeneous (X j) _ _ hQ
  simp only [rename_X] at hh
  have hd := hh.degree_unique (M.group.ambient.isHomogeneous_X (M.variableEquiv j))
    (X_ne_zero (M.variableEquiv j))
  have h0 := congrFun hd (0 : Fin 2)
  by_cases hj : j.val < 2
  · simpa [hj, eq_comm] using h0.symm
  · have hne : (M.variableEquiv j).1 ≠ (0 : Fin 2) := by
      intro h
      simp [hj, h] at h0
    simp only [if_neg hj]
    have hlt := (M.variableEquiv j).1.isLt
    change (M.variableEquiv j).1.val < 2 at hlt
    apply Fin.ext
    change (M.variableEquiv j).1.val = 1
    have hv : (M.variableEquiv j).1.val ≠ 0 := fun h => hne (Fin.ext h)
    omega

theorem exponent_block_sums (d : Fin 7 →₀ ℕ) (i : Fin 2) :
    (∑ j : Fin ((M.factor i).ambientDimension + 1),
      (d.mapDomain M.variableEquiv) ⟨i, j⟩) =
      if i = 0 then d 0 + d 1 else d 2 + d 3 + d 4 + d 5 + d 6 := by
  classical
  have hall : (∑ v : M.group.ambient.Variable,
      if v.1 = i then (d.mapDomain M.variableEquiv) v else 0) =
      ∑ j : Fin 7, if (M.variableEquiv j).1 = i then d j else 0 := by
    rw [← M.variableEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finsupp.mapDomain_apply M.variableEquiv.injective]
  rw [Fintype.sum_sigma] at hall
  change (∑ k : Fin 2, ∑ j : Fin ((M.factor k).ambientDimension + 1),
    if k = i then (d.mapDomain M.variableEquiv) ⟨k, j⟩ else 0) = _ at hall
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hall
  rw [hall]
  simp only [M.variableEquiv_block]
  fin_cases i <;> simp [Fin.sum_univ_seven]

theorem homogeneous_iff (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) :
    M.group.ambient.IsHomogeneous (rename M.variableEquiv Q) ![m, n] ↔
      Bihomogeneous Q m n := by
  classical
  constructor
  · intro h d hd
    have hd' : d.mapDomain M.variableEquiv ∈ (rename M.variableEquiv Q).support := by
      rw [support_rename_of_injective M.variableEquiv.injective]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have h0 := h _ hd' (0 : Fin 2)
    have h1 := h _ hd' (1 : Fin 2)
    change (∑ j : Fin ((M.factor 0).ambientDimension + 1),
      (d.mapDomain M.variableEquiv) ⟨(0 : Fin 2), j⟩) = m at h0
    change (∑ j : Fin ((M.factor 1).ambientDimension + 1),
      (d.mapDomain M.variableEquiv) ⟨(1 : Fin 2), j⟩) = n at h1
    rw [M.exponent_block_sums] at h0 h1
    exact ⟨by simpa using h0, by simpa using h1⟩
  · exact M.homogeneous Q m n

/-- Proper closed subgroups supply the actual bihomogeneous polynomial
constraint needed by the application argument. -/
theorem exists_bihomogeneous_subgroup_separator (H : AlgebraicSubgroup M.group)
    (hproper : H.carrier ≠ Set.univ) :
    ∃ Q : MvPolynomial (Fin 7) ℂ, ∃ m n : ℕ,
      Bihomogeneous Q m n ∧
      (∀ g ∈ H.carrier, g ∈ zeroLocusOnGroup M.group (M.polynomial Q)) ∧
      ∃ v : ℂ, eval (rawCoordinates S v) Q ≠ 0 := by
  obtain ⟨P, D, hP, hzero, g, ⟨v, rfl⟩, hne⟩ :=
    M.group.exists_homogeneous_separator (Set.range M.curve) H.carrier
      M.curve_dense H.isClosed hproper
  let Q := rename M.variableEquiv.symm P
  have hrename : rename M.variableEquiv Q = P := by
    simp [Q, rename_rename]
  have hD : D = ![D 0, D 1] := by
    funext i
    change Fin 2 at i
    fin_cases i <;> rfl
  have hQ : Bihomogeneous Q (D 0) (D 1) := (M.homogeneous_iff Q _ _).mp (by
    rw [hrename]
    simpa only [← hD] using hP)
  refine ⟨Q, D 0, D 1, hQ, ?_, v, ?_⟩
  · intro g hg
    change M.group.ambient.eval (rename M.variableEquiv Q) (M.group.embedding g) = 0
    rw [hrename]
    exact hzero g hg
  · intro hz
    have hh := (M.zero_locus Q _ _ hQ v).mpr hz
    change M.group.ambient.eval (rename M.variableEquiv Q) (M.group.embedding (M.curve v)) = 0 at hh
    rw [hrename] at hh
    exact hne hh

/-- The first factor of the modeled curve detects its complex parameter. -/
theorem curve_first_factor_eq_zero_iff (v : ℂ) : M.curve v 0 = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hQ : Bihomogeneous (X (1 : Fin 7)) 1 0 := by
      intro d hd
      simp only [support_X, Finset.mem_singleton] at hd
      subst d
      simp
    have hb : (M.variableEquiv 1).1 = (0 : Fin 2) := by
      simpa using M.variableEquiv_block 1
    have hi : M.curve v (M.variableEquiv 1).1 = (0 : M.group.Point) (M.variableEquiv 1).1 := by
      have hall (i : Fin 2) (h : i = 0) : M.curve v i = (0 : M.group.Point) i := by
        subst i
        exact hv
      exact hall _ hb
    have heval : M.group.ambient.eval (rename M.variableEquiv (X (1 : Fin 7)))
        (M.group.embedding (M.curve v)) =
        M.group.ambient.eval (rename M.variableEquiv (X (1 : Fin 7)))
          (M.group.embedding 0) := by
      simp only [MultiProjectiveSpace.eval, rename_X, eval_X,
        MultiProjectiveSpace.coordinate, EmbeddedGroupProduct.embedding]
      exact congrArg (fun p => p.val.rep (M.variableEquiv 1).2) hi
    have hz := (M.zero_locus (X (1 : Fin 7)) 1 0 hQ 0).mpr (by simp [rawCoordinates])
    change M.group.ambient.eval (rename M.variableEquiv (X (1 : Fin 7)))
      (M.group.embedding (M.curve 0)) = 0 at hz
    have hz' : M.group.ambient.eval (rename M.variableEquiv (X (1 : Fin 7)))
        (M.group.embedding 0) = 0 := by simpa only [map_zero] using hz
    have hv' := (M.zero_locus (X (1 : Fin 7)) 1 0 hQ v).mp (heval.trans hz')
    simpa [rawCoordinates] using hv'
  · rintro rfl
    simp

/-- The paper's subgroups with zero additive projection meet the modeled curve
only at its identity. No classification or degree assertion is assumed here. -/
theorem pullbackSubmodule_eq_bot_of_first_factor_zero (H : AlgebraicSubgroup M.group)
    (hH : ∀ g ∈ H.carrier, g 0 = 0) : M.pullbackSubmodule H = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro v hv
  change v = 0
  exact (M.curve_first_factor_eq_zero_iff v).mp (hH (M.curve v) hv)

end WeierstrassEllipticZeta.PhilipponApplication.Model
end

-- Source: Solutions/PhilipponProjectivePointSeparation.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MvPolynomial
namespace PhilipponMultiplicity.MultiProjectiveSpace

/-- Multihomogeneous equations distinguish actual projective points. -/
theorem point_eq_of_homogeneous_implication {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (x y : M.Point)
    (h : ∀ (P : M.CoordinateRing) (D : M.FactorIndex → ℕ),
      M.IsHomogeneous P D → M.eval P y = 0 → M.eval P x = 0) : x = y := by
  classical
  funext i
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (Projectivization.rep_nonzero (y i))
  change (y i).rep k ≠ 0 at hk
  have heq (j : Fin (M.ambientDimension i + 1)) :
      (y i).rep k * (x i).rep j - (y i).rep j * (x i).rep k = 0 := by
    have hP := (M.isHomogeneous_X ⟨i, j⟩).C_mul M ((y i).rep k)
    have hQ := (M.isHomogeneous_X ⟨i, k⟩).C_mul M ((y i).rep j)
    have hh := h _ _ (hP.sub M hQ) (by simp [eval, coordinate, mul_comm])
    simpa [eval, coordinate] using hh
  rw [← Projectivization.mk_rep (x i), ← Projectivization.mk_rep (y i)]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  exact ⟨(x i).rep k / (y i).rep k, by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    simpa only [mul_comm] using (sub_eq_zero.mp (heq j)).symm⟩

end PhilipponMultiplicity.MultiProjectiveSpace

namespace WeierstrassEllipticZeta.PhilipponApplication.Model
open PhilipponMultiplicity

/-- A subgroup with exactly the homogeneous equations of the identity is the
identity subgroup. This retains the arbitrary compatible Model. -/
theorem carrier_eq_singleton_of_identity_equations {S : Fin 5 → ℂ → ℂ}
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (h : M.HasParametricEquations H (fun _ : Unit => rawCoordinates S 0)) :
    H.carrier = {0} := by
  apply Set.Subset.antisymm
  · intro g hg
    have he : M.group.embedding g = M.group.embedding 0 := by
      apply M.group.ambient.point_eq_of_homogeneous_implication
      intro P degrees hP hzero
      change Fin 2 → ℕ at degrees
      let Q := rename M.variableEquiv.symm P
      have hrename : rename M.variableEquiv Q = P := by simp [Q, rename_rename]
      have hd : degrees = ![degrees 0, degrees 1] := by
        funext i
        change Fin 2 at i
        fin_cases i <;> rfl
      have hQ : Bihomogeneous Q (degrees 0) (degrees 1) := (M.homogeneous_iff Q _ _).mp (by
        rw [hrename, ← hd]
        exact hP)
      have hraw : MvPolynomial.eval (rawCoordinates S 0) Q = 0 := by
        apply (M.zero_locus Q _ _ hQ 0).mp
        change M.group.ambient.eval (rename M.variableEquiv Q)
          (M.group.embedding (M.curve 0)) = 0
        simpa only [hrename, map_zero] using hzero
      have hall := (h Q _ _ hQ).mpr (fun _ => hraw)
      simpa only [polynomial, hrename] using hall g hg
    have hg0 : g = 0 := by
      funext i
      exact Subtype.ext (congrFun he i)
    exact Set.mem_singleton_iff.mpr hg0
  · intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact H.toAddSubgroup.zero_mem

end WeierstrassEllipticZeta.PhilipponApplication.Model
end

noncomputable section
namespace PhilipponMultiplicity
def additivePoint (K : Type*) [Field K] (z : K) : Projectivization K (Fin 2 → K) :=
  Projectivization.mk K ![1, z] (by intro h; have := congrFun h 0; simpa using this)
end PhilipponMultiplicity
end

-- Source: Solutions/WeierstrassProductCoordinates.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators
open MvPolynomial TranscendenceTheory PhilipponMultiplicity
namespace WeierstrassEllipticZeta

abbrev extensionProductAmbient : MultiProjectiveSpace ℂ := ⟨2, by decide, ![1, 4]⟩

abbrev ExtensionProductVariable := Sigma fun i : Fin 2 => Fin (![1, 4] i + 1)

def extensionProductVariableEquiv : Fin 7 ≃ ExtensionProductVariable where
  toFun := ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 3⟩, ⟨1, 4⟩]
  invFun := fun s => if h : s.1 = 0 then
      ⟨s.2.val, by have := s.2.isLt; simp only [h] at this; norm_num at this; omega⟩
    else ⟨s.2.val + 2, by
      have hs : s.1 = 1 := by omega
      have hh := s.2.isLt
      simp only [hs] at hh
      norm_num at hh
      omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv s := by
    rcases s with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> rfl

def extensionProductEmbedding {g₂ g₃ : ℂ}
    (p : ℂ × ProjectiveExtensionChartLocus g₂ g₃) : extensionProductAmbient.Point :=
  Fin.cons (additivePoint ℂ p.1) (Fin.cons p.2.val.val (fun i => Fin.elim0 i))

private theorem product_exponent_sums (d : Fin 7 →₀ ℕ) :
    (∑ j : Fin 2, (d.mapDomain extensionProductVariableEquiv) ⟨(0 : Fin 2), j⟩) =
        d 0 + d 1 ∧
    (∑ j : Fin 5, (d.mapDomain extensionProductVariableEquiv) ⟨(1 : Fin 2), j⟩) =
        d 2 + d 3 + d 4 + d 5 + d 6 := by
  have h0 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 0
  have h1 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 1
  have h2 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 2
  have h3 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 3
  have h4 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 4
  have h5 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 5
  have h6 := Finsupp.mapDomain_apply extensionProductVariableEquiv.injective d 6
  change (d.mapDomain extensionProductVariableEquiv) ⟨0, 0⟩ = d 0 at h0
  change (d.mapDomain extensionProductVariableEquiv) ⟨0, 1⟩ = d 1 at h1
  change (d.mapDomain extensionProductVariableEquiv) ⟨1, 0⟩ = d 2 at h2
  change (d.mapDomain extensionProductVariableEquiv) ⟨1, 1⟩ = d 3 at h3
  change (d.mapDomain extensionProductVariableEquiv) ⟨1, 2⟩ = d 4 at h4
  change (d.mapDomain extensionProductVariableEquiv) ⟨1, 3⟩ = d 5 at h5
  change (d.mapDomain extensionProductVariableEquiv) ⟨1, 4⟩ = d 6 at h6
  simp only [Fin.sum_univ_two, Fin.sum_univ_five, h0, h1, h2, h3, h4, h5, h6, and_self]

theorem extensionProduct_homogeneous_iff (Q : MvPolynomial (Fin 7) ℂ)
    (D : Fin 2 → ℕ) :
    extensionProductAmbient.IsHomogeneous (rename extensionProductVariableEquiv Q) D ↔
      ∀ d ∈ Q.support, d 0 + d 1 = D 0 ∧ d 2 + d 3 + d 4 + d 5 + d 6 = D 1 := by
  classical
  unfold MultiProjectiveSpace.IsHomogeneous
  rw [support_rename_of_injective extensionProductVariableEquiv.injective]
  constructor
  · intro h d hd
    have hh := h _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
    exact ⟨(product_exponent_sums d).1.symm.trans (hh 0),
      (product_exponent_sums d).2.symm.trans (hh 1)⟩
  · intro h d hd i
    obtain ⟨c, hc, hcd⟩ := Finset.mem_image.mp hd
    subst d
    change Fin 2 at i
    fin_cases i
    · exact (product_exponent_sums c).1.trans (h c hc).1
    · exact (product_exponent_sums c).2.trans (h c hc).2

private theorem product_block_scale (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (v : Fin 7 → ℂ) (a b : ℂ) :
    eval ![a * v 0, a * v 1, b * v 2, b * v 3, b * v 4, b * v 5, b * v 6] Q =
      a ^ m * b ^ n * eval v Q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← (hQ d hd).1, ← (hQ d hd).2]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

theorem extensionProduct_eval_zero_iff (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n)
    {g₂ g₃ : ℂ} (p : ℂ × ProjectiveExtensionChartLocus g₂ g₃) :
    extensionProductAmbient.eval (rename extensionProductVariableEquiv Q)
      (extensionProductEmbedding p) = 0 ↔
    eval ![1, p.1, p.2.val.val.rep 0, p.2.val.val.rep 1, p.2.val.val.rep 2,
      p.2.val.val.rep 3, p.2.val.val.rep 4] Q = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ ![1, p.1]
    (by intro h; have := congrFun h 0; simpa using this)
  change eval (extensionProductAmbient.coordinate (extensionProductEmbedding p))
    (rename extensionProductVariableEquiv Q) = 0 ↔ _
  rw [eval_rename]
  have hv : (fun i => extensionProductAmbient.coordinate (extensionProductEmbedding p)
      (extensionProductVariableEquiv i)) =
      ![a.val, a.val * p.1, p.2.val.val.rep 0, p.2.val.val.rep 1,
        p.2.val.val.rep 2, p.2.val.val.rep 3, p.2.val.val.rep 4] := by
    funext i
    fin_cases i <;>
      simp [extensionProductAmbient, MultiProjectiveSpace.coordinate, extensionProductEmbedding,
        extensionProductVariableEquiv, additivePoint, ← ha, Units.smul_def]
  have heval : eval (extensionProductAmbient.coordinate (extensionProductEmbedding p) ∘
      extensionProductVariableEquiv) Q =
      eval ![a.val, a.val * p.1, p.2.val.val.rep 0, p.2.val.val.rep 1,
        p.2.val.val.rep 2, p.2.val.val.rep 3, p.2.val.val.rep 4] Q :=
    congrArg (fun f : Fin 7 → ℂ => eval f Q) hv
  rw [heval]
  have hscale := product_block_scale Q m n hQ
    ![1, p.1, p.2.val.val.rep 0, p.2.val.val.rep 1, p.2.val.val.rep 2,
      p.2.val.val.rep 3, p.2.val.val.rep 4] a.val 1
  simp at hscale
  rw [hscale]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ a.ne_zero))

theorem extensionProduct_raw_eval_zero_iff (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n)
    {g₂ g₃ : ℂ} (p : ℂ × ProjectiveExtensionChartLocus g₂ g₃)
    (v : Fin 5 → ℂ) (hv : v ≠ 0) (hp : p.2.val.val = Projectivization.mk ℂ v hv) :
    extensionProductAmbient.eval (rename extensionProductVariableEquiv Q)
      (extensionProductEmbedding p) = 0 ↔
    eval ![1, p.1, v 0, v 1, v 2, v 3, v 4] Q = 0 := by
  rw [extensionProduct_eval_zero_iff Q m n hQ p]
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [hp, ← hb]
  simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul]
  have hscale := product_block_scale Q m n hQ ![1, p.1, v 0, v 1, v 2, v 3, v 4] 1 b.val
  simp at hscale
  rw [hscale]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ b.ne_zero))

end WeierstrassEllipticZeta

end

-- Source: Solutions/WeierstrassBoundaryNormalization.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open PhilipponMultiplicity TranscendenceTheory MvPolynomial
namespace WeierstrassEllipticZeta

theorem extension_boundary_coordinates (g₂ g₃ : ℂ)
    (p : ProjectiveExtensionChartLocus g₂ g₃) (s : Fin 5 → ℂ)
    (hs : s ≠ 0) (hp : p.val.val = Projectivization.mk ℂ s hs) (h0 : s 0 = 0) :
    s 1 = 0 ∧ s 2 ≠ 0 ∧ s 3 = 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ s hs
  have hr : p.val.val.rep = c • s := by rw [hp, hc]
  have h2 : s 2 ≠ 0 := by
    have h := p.property
    rw [hr] at h
    simpa [h0, Units.smul_def, c.ne_zero] using h
  have h1 : s 1 = 0 := by
    have h := p.val.property.2
    rw [hr] at h
    simpa [extensionCubic, Units.smul_def, h0, c.ne_zero] using h
  have h3 : s 3 = 0 := by
    have h := p.val.property.1
    rw [hr] at h
    simpa [extensionQuadric, Units.smul_def, h0, h1, h2, c.ne_zero] using h
  exact ⟨h1, h2, h3⟩
end WeierstrassEllipticZeta
end

-- Source: Solutions/WeierstrassAdditivePlaneProfile.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open PhilipponMultiplicity TranscendenceTheory
namespace WeierstrassEllipticZeta

/-- Entire Weierstrass lifts have vanishing first coordinate at the origin. -/
theorem entire_weierstrass_origin_coordinate (L : PeriodPair)
    (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    S 0 0 = 0 := by
  have hS0 : S 0 = fun z => D.sigma z ^ 3 := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (hS 0)
      (fun z _ => (D.entire.analyticAt z).pow 3) (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with z hz
    simpa using hS_value z hz 0
  simp [hS0, D.zero]
end WeierstrassEllipticZeta
end

-- Source: Solutions/WeierstrassEquationalClassification.lean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial PhilipponMultiplicity TranscendenceTheory
namespace WeierstrassEllipticZeta
open PhilipponApplication

variable (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)

private theorem linear_coordinate_line
    (V : Submodule ℂ (Fin 3 → ℂ)) (v : V) (hv1 : v.val 1 ≠ 0)
    (Q : MvPolynomial (Fin 7) ℂ)
    (hzero : ∀ w : V, eval (exponentialCoordinates S w.val) Q = 0) (z : ℂ) :
    eval (exponentialCoordinates S ![(v.val 0 / v.val 1) * z, z,
      (v.val 2 / v.val 1) * z]) Q = 0 := by
  have hh := hzero ((z / v.val 1) • v)
  have he : ((z / v.val 1) • v).val =
      ![(v.val 0 / v.val 1) * z, z, (v.val 2 / v.val 1) * z] := by
    funext i
    fin_cases i
    · simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    · exact div_mul_cancel₀ z hv1
    · simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rwa [he] at hh

include hS hS_value hS_ne in
private theorem coordinate_subspace_projection_cases
    (V : Submodule ℂ (Fin 3 → ℂ)) (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hzero : ∀ v : V, eval (exponentialCoordinates S v.val) Q = 0)
    (hne : ∃ z : ℂ, eval (rawCoordinates S z) Q ≠ 0) :
    (∀ v : V, v.val 0 = 0) ∨ (∀ v : V, v.val 1 = 0) := by
  have hpoint (v : V) : v.val 0 = 0 ∨ v.val 1 = 0 := by
    by_contra! hn
    have hs := projective_linear_direction_saturation L D S hS hS_value hS_ne Q n hQ
      (v.val 0 / v.val 1) (v.val 2 / v.val 1) (linear_coordinate_line S V v hn.2 Q hzero)
    obtain ⟨z, hz⟩ := hne
    have hh := hs (z / (v.val 0 / v.val 1)) z 0
    rw [mul_div_cancel₀ _ (div_ne_zero hn.1 hn.2)] at hh
    exact hz (by simpa [rawCoordinates] using hh)
  by_cases hfirst : ∀ v : V, v.val 0 = 0
  · exact Or.inl hfirst
  · push Not at hfirst
    obtain ⟨v, hv0⟩ := hfirst
    have hv1 : v.val 1 = 0 := (hpoint v).resolve_left hv0
    right
    intro w
    by_contra hw1
    have hw0 : w.val 0 = 0 := (hpoint w).resolve_right hw1
    rcases hpoint (v + w) with h | h
    · exact hv0 (by simpa [hw0] using h)
    · exact hw1 (by simpa [hv1] using h)

private theorem last_block_scale (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (v : Fin 7 → ℂ) (r : ℂ) :
    eval ![v 0, v 1, r * v 2, r * v 3, r * v 4, r * v 5, r * v 6] Q =
      r ^ n * eval v Q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← hQ d hd]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

private theorem plane_submodule_cases (W : Submodule ℂ (ℂ × ℂ)) :
    W = ⊥ ∨ W = ⊤ ∨ ∃ v : ℂ × ℂ, v ≠ 0 ∧
      (W : Set (ℂ × ℂ)) = Set.range (fun c : ℂ => c • v) := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  by_cases ht : W = ⊤
  · exact Or.inr (Or.inl ht)
  have hdim : Module.finrank ℂ W = 1 := by
    have hp : Module.finrank ℂ W ≠ 0 := fun h => hb (Submodule.finrank_eq_zero.mp h)
    have hl := Submodule.finrank_lt ht
    have ha : Module.finrank ℂ (ℂ × ℂ) = 2 := by simp [Module.finrank_prod]
    omega
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.mp hdim
  refine Or.inr (Or.inr ⟨v.val, (fun h => hv (Subtype.ext h)), ?_⟩)
  ext w
  constructor
  · intro hw
    obtain ⟨c, hc⟩ := hspan ⟨w, hw⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  · rintro ⟨c, rfl⟩
    exact W.smul_mem c v.property

include hS hS_value hS_ne in
/-- All cases of Lemma A.1 follow from the linear exponential equation
description. This proves the geometric classification implication for every
compatible Model; existence of the description remains a separate theorem. -/
theorem subgroup_paper_type_of_linear_equations
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hproper : H.carrier ≠ Set.univ) (hlinear : M.HasLinearSubgroupEquations H) :
    M.HasPaperSubgroupType L H := by
  obtain ⟨V, hV⟩ := hlinear
  obtain ⟨Q, m, n, hQ, hzero, hne⟩ := M.exists_bihomogeneous_subgroup_separator H hproper
  have hVzero := (hV Q m n hQ).mp hzero
  have hcases := coordinate_subspace_projection_cases L D S hS hS_value hS_ne
    V Q n (fun d hd => (hQ d hd).2) hVzero hne
  obtain ⟨η, hη, _⟩ := elliptic_extension_group_geometry L
  obtain ⟨group, hgroup⟩ := projective_extension_group_with_regular_negation L D S hS hS_value hS_ne η hη
  letI := group
  obtain ⟨e, he, _⟩ := hgroup
  by_cases hz : ∀ v : V, v.val 1 = 0
  · have h0 := entire_weierstrass_origin_coordinate L D S hS hS_value
    obtain ⟨hs0, hp0⟩ := he 0 0
    obtain ⟨h1, h2, h3⟩ := extension_boundary_coordinates L.g₂ L.g₃ _ _ hs0 hp0 (by simpa using h0)
    change S 1 0 = 0 at h1
    change S 2 0 ≠ 0 at h2
    have h3 : S 3 0 = 0 := by simpa using h3
    let ρ := S 4 0 / S 2 0
    let π : (Fin 3 → ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
      (LinearMap.proj 0).prod (LinearMap.proj 2)
    let W := V.map π
    have hnorm (P : MvPolynomial (Fin 7) ℂ) (a b : ℕ)
        (hP : Bihomogeneous P a b) (v : V) :
        eval (exponentialCoordinates S v.val) P = 0 ↔
          eval ![1, v.val 0, 0, 0, 1, 0, ρ + v.val 2] P = 0 := by
      have hscale := last_block_scale P b (fun d hd => (hP d hd).2)
        ![1, v.val 0, 0, 0, 1, 0, ρ + v.val 2] (S 2 0)
      have hv : exponentialCoordinates S v.val =
          ![1, v.val 0, 0, 0, S 2 0, 0, S 2 0 * (ρ + v.val 2)] := by
        funext i
        fin_cases i <;> simp [exponentialCoordinates, hz v, h0, h1, h3, ρ,
          mul_add, mul_div_cancel₀ _ h2, mul_comm]
      rw [hv]
      have heval : eval ![1, v.val 0, 0, 0, S 2 0, 0, S 2 0 * (ρ + v.val 2)] P =
          S 2 0 ^ b * eval ![1, v.val 0, 0, 0, 1, 0, ρ + v.val 2] P := by
        simpa using hscale
      rw [heval]
      exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ h2))
    have hW : M.HasParametricEquations H
        (fun w : W => ![1, w.val.1, 0, 0, 1, 0, ρ + w.val.2]) := by
      intro P a b hP
      refine (hV P a b hP).trans ⟨?_, ?_⟩
      · intro hh w
        obtain ⟨v, hv, hvw⟩ := w.property
        have h := (hnorm P a b hP ⟨v, hv⟩).mp (hh ⟨v, hv⟩)
        change (v 0, v 2) = w.val at hvw
        simpa only [← hvw] using h
      · intro hh v
        exact (hnorm P a b hP v).mpr (hh ⟨π v.val, ⟨v.val, v.property, rfl⟩⟩)
    rcases plane_submodule_cases W with hb | ht | ⟨w, hw, hr⟩
    · left
      apply M.carrier_eq_singleton_of_identity_equations H
      have hv0 (v : V) : v.val = 0 := by
        have hmem : π v.val ∈ W := ⟨v.val, v.property, rfl⟩
        rw [hb] at hmem
        change (v.val 0, v.val 2) = 0 at hmem
        funext i
        fin_cases i
        · exact congrArg Prod.fst hmem
        · exact hz v
        · exact congrArg Prod.snd hmem
      intro P a b hP
      refine (hV P a b hP).trans ⟨?_, ?_⟩
      · intro hh _
        simpa [exponentialCoordinates, rawCoordinates] using hh 0
      · intro hh v
        simpa [hv0 v, exponentialCoordinates, rawCoordinates] using hh ()
    · right; right; left
      refine ⟨ρ, ?_⟩
      intro P a b hP
      refine (hW P a b hP).trans ⟨?_, ?_⟩
      · intro hh t
        exact hh ⟨(t 0, t 1), by rw [ht]; trivial⟩
      · intro hh w
        exact hh ![w.val.1, w.val.2]
    · right; right; right
      have hw' : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
        by_contra! hh
        exact hw (Prod.ext hh.1 hh.2)
      refine ⟨w.1, w.2, ρ, hw', ?_⟩
      intro P a b hP
      refine (hW P a b hP).trans ⟨?_, ?_⟩
      · intro hh t
        have ht : (w.1 * t, w.2 * t) ∈ W := by
          change (w.1 * t, w.2 * t) ∈ (W : Set (ℂ × ℂ))
          rw [hr]
          exact ⟨t, by ext <;> simp [mul_comm]⟩
        exact hh ⟨_, ht⟩
      · intro hh x
        have hx : x.val ∈ (W : Set (ℂ × ℂ)) := x.property
        rw [hr] at hx
        obtain ⟨t, ht⟩ := hx
        have ht' : x.val = (w.1 * t, w.2 * t) := by
          rw [← ht]
          ext <;> simp [mul_comm]
        simpa only [ht'] using hh t
  · have hfirst := hcases.resolve_right hz
    push Not at hz
    obtain ⟨v, hv1⟩ := hz
    right; left
    intro P a b hP
    refine (hV P a b hP).trans ⟨?_, ?_⟩
    · intro hh p
      have hline := linear_coordinate_line S V v hv1 P hh
      rw [hfirst v, zero_div] at hline
      have hfull := projective_linear_direction_saturation L D S hS hS_value hS_ne P b
        (fun d hd => (hP d hd).2) 0 (v.val 2 / v.val 1) hline
      obtain ⟨q, rfl⟩ := e.surjective p
      obtain ⟨⟨z, u⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective q
      obtain ⟨hv, hp⟩ := he z u
      have hraw := hfull 0 z u
      have hproj := (extensionProduct_raw_eval_zero_iff P a b hP
        (0, e ((extensionPeriodGraph L.lattice η).mkQ (z, u))) _ hv hp).mpr (by simpa using hraw)
      simpa using (extensionProduct_eval_zero_iff P a b hP
        (0, e ((extensionPeriodGraph L.lattice η).mkQ (z, u)))).mp hproj
    · intro hh w
      obtain ⟨hv, hp⟩ := he (w.val 1) (w.val 2)
      have hproj := (extensionProduct_eval_zero_iff P a b hP
        (0, e ((extensionPeriodGraph L.lattice η).mkQ (w.val 1, w.val 2)))).mpr (hh _)
      have hraw := (extensionProduct_raw_eval_zero_iff P a b hP
        (0, e ((extensionPeriodGraph L.lattice η).mkQ (w.val 1, w.val 2))) _ hv hp).mp hproj
      simpa [exponentialCoordinates, hfirst w] using hraw

end WeierstrassEllipticZeta
end

open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication PhilipponMultiplicity
theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (M : Model S) (H : AlgebraicSubgroup M.group)
    (hproper : H.carrier ≠ Set.univ) (hlinear : M.HasLinearSubgroupEquations H) :
    M.HasPaperSubgroupType L H := by
  exact WeierstrassEllipticZeta.subgroup_paper_type_of_linear_equations L D S hS hS_value hS_ne M H hproper hlinear
#print axioms solution
