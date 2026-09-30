-- Prove2me | solution 1 for WeierstrassEllipticZeta.translated_subgroup_polynomial_constraint
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T05:21:52.382386+00:00
-- url     : https://prove2.me/submissions/34e45b3f-5478-48fa-8430-237b15f9bd9a

import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_differential_data
import Theorems.Thm_WeierstrassEllipticZeta_sigma_addition_from_differential
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Algebra.BigOperators.Fin


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


noncomputable section
open MvPolynomial WeierstrassEllipticZeta
open scoped Topology

namespace WeierstrassEllipticZeta

private lemma last_block_scaling (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (x : Fin 7 → ℂ) (r : ℂ) :
    eval ![x 0, x 1, r * x 2, r * x 3, r * x 4, r * x 5, r * x 6] Q =
      r ^ n * eval x Q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← hQ d hd]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

private lemma normalize_regular_eval (Q : MvPolynomial (Fin 7) ℂ)
    (t x y u : ℂ) :
    eval ![t, x, y, u] (extensionChartNormalize 0 Q) =
      eval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] Q := by
  change (aeval ![t, x, y, u]) ((aeval (extensionChartSubstitution 0)) Q) = _
  rw [comp_aeval_apply]
  apply congrArg (fun v : Fin 7 → ℂ => eval v Q)
  funext i
  fin_cases i <;> simp [extensionChartSubstitution]

/-- A nonzero entire projective pullback is already nonzero on the regular
affine chart. Thus dehomogenization supplies the properness witness required by
the analytic subgroup criterion, including when the original nonzero value was
at a lattice point. -/
theorem projective_nonzero_regular_chart_witness
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0) :
    ∃ z : ℂ, z ∉ L.lattice ∧
      eval ![z, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z] (extensionChartNormalize 0 Q) ≠ 0 := by
  classical
  by_contra! hzero
  apply hne
  have hF : AnalyticOnNhd ℂ (fun z : ℂ => eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) Set.univ := by
    intro z _
    apply AnalyticAt.aeval_mvPolynomial
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_id
    · exact hS 0 z (Set.mem_univ z)
    · exact hS 1 z (Set.mem_univ z)
    · exact hS 2 z (Set.mem_univ z)
    · exact hS 3 z (Set.mem_univ z)
    · exact hS 4 z (Set.mem_univ z)
  apply AnalyticOnNhd.eq_of_eventuallyEq hF
    (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
    (z₀ := L.ω₁ / 2)
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds L.ω₁_div_two_notMem_lattice]
    with z hz
  change eval ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q = 0
  have he := last_block_scaling Q n hQ
    ![1, z, 1, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z,
      L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2]
    (D.sigma z ^ 3)
  rw [← normalize_regular_eval] at he
  simpa [hS_value z hz, hzero z hz] using he

end WeierstrassEllipticZeta


noncomputable section
open MvPolynomial WeierstrassEllipticZeta
open scoped Classical

namespace WeierstrassEllipticZeta

/-- Translating a polynomially constrained analytic subgroup does not change the
two possible projection kernels. All three translation coordinates are arbitrary. -/
theorem affine_coset_polynomial_profile (L : PeriodPair)
    (V : Submodule ℂ (Fin 3 → ℂ)) (r : Fin 3 → ℂ)
    (P : MvPolynomial (Fin 4) ℂ)
    (hproper : ∃ z : ℂ, z ∉ L.lattice ∧
      eval ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z] P ≠ 0)
    (hvanish : ∀ v ∈ V, r 1 + v 1 ∉ L.lattice →
      eval ![r 0 + v 0, L.weierstrassP (r 1 + v 1),
        L.derivWeierstrassP (r 1 + v 1), r 2 + v 2 + weierstrassZeta L (r 1 + v 1)]
          P = 0) :
    (∀ v ∈ V, v 0 = 0) ∨ (∀ v ∈ V, v 1 = 0) := by
  have hpoint (v : Fin 3 → ℂ) (hv : v ∈ V) : v 0 = 0 ∨ v 1 = 0 := by
    by_contra! h
    let α := v 0 / v 1
    let β := v 2 / v 1
    let δt := r 0 - α * r 1
    let δu := r 2 - β * r 1
    let R : MvPolynomial (Fin 4) ℂ :=
      aeval ![X 0 + C δt, X 1, X 2, X 3 + C δu] P
    have heval (t x y u : ℂ) : eval ![t, x, y, u] R =
        eval ![t + δt, x, y, u + δu] P := by
      change (aeval ![t, x, y, u])
        ((aeval ![X 0 + C δt, X 1, X 2, X 3 + C δu]) P) = _
      rw [comp_aeval_apply]
      apply congrArg (fun w : Fin 4 → ℂ => eval w P)
      funext i
      fin_cases i <;> simp
    have hline (z : ℂ) (hz : z ∉ L.lattice) :
        eval ![α * z, L.weierstrassP z, L.derivWeierstrassP z,
          weierstrassZeta L z + β * z] R = 0 := by
      have hzval : r 1 + (((z - r 1) / v 1) • v) 1 = z := by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [div_mul_cancel₀ _ h.2]
        ring
      have hh := hvanish _ (V.smul_mem ((z - r 1) / v 1) hv) (by rwa [hzval])
      rw [hzval] at hh
      rw [heval]
      convert hh using 1
      apply congrArg (fun w : Fin 4 → ℂ => eval w P)
      funext i
      fin_cases i <;> simp [α, β, δt, δu, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv] <;> ring
    obtain ⟨z, hz, hne⟩ := hproper
    have he := linear_direction_polynomial_saturation L α β (div_ne_zero h.1 h.2)
      R hline z hz (z - δt) (weierstrassZeta L z - δu)
    rw [heval, sub_add_cancel, sub_add_cancel] at he
    exact hne he
  by_cases ht : ∀ v ∈ V, v 0 = 0
  · exact Or.inl ht
  · push Not at ht
    obtain ⟨v, hv, hv0⟩ := ht
    have hv1 : v 1 = 0 := (hpoint v hv).resolve_left hv0
    right
    intro w hw
    by_contra hw1
    have hw0 : w 0 = 0 := (hpoint w hw).resolve_right hw1
    rcases hpoint (v + w) (V.add_mem hv hw) with h | h
    · exact hv0 (by simpa [hw0] using h)
    · exact hw1 (by simpa [hv1] using h)

private lemma translated_block_scaling (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (x : Fin 7 → ℂ) (s : ℂ) :
    eval ![x 0, x 1, s * x 2, s * x 3, s * x 4, s * x 5, s * x 6] Q =
      s ^ n * eval x Q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← hQ d hd]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

private lemma translated_normalize_eval (Q : MvPolynomial (Fin 7) ℂ)
    (t x y u : ℂ) :
    eval ![t, x, y, u] (extensionChartNormalize 0 Q) =
      eval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] Q := by
  change (aeval ![t, x, y, u]) ((aeval (extensionChartSubstitution 0)) Q) = _
  rw [comp_aeval_apply]
  apply congrArg (fun v : Fin 7 → ℂ => eval v Q)
  funext i
  fin_cases i <;> simp [extensionChartSubstitution]


end WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0)
    (V : Submodule ℂ (Fin 3 → ℂ)) (r : Fin 3 → ℂ)
    (hvanish : ∀ v ∈ V,
      eval ![1, r 0 + v 0, S 0 (r 1 + v 1), S 1 (r 1 + v 1),
        S 2 (r 1 + v 1), S 3 (r 1 + v 1) + (r 2 + v 2) * S 0 (r 1 + v 1),
        S 4 (r 1 + v 1) + (r 2 + v 2) * S 2 (r 1 + v 1)] Q = 0) :
    ∃ P : MvPolynomial (Fin 4) ℂ,
      (∃ z : ℂ, z ∉ L.lattice ∧
        eval ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z] P ≠ 0) ∧
      (∀ v ∈ V, v 1 ∉ L.lattice →
        eval ![v 0, L.weierstrassP (v 1), L.derivWeierstrassP (v 1),
          v 2 + weierstrassZeta L (v 1)] P = 0) := by
  have hproper := projective_nonzero_regular_chart_witness L D S hS hS_value Q n hQ hne
  have hσ (z : ℂ) (hz : z ∉ L.lattice) : D.sigma z ≠ 0 := by
    intro hzero
    obtain ⟨j, hj⟩ := hS_ne z
    exact hj (by simp [hS_value z hz j, hzero])
  have haffine (v : Fin 3 → ℂ) (hv : v ∈ V) (hz : r 1 + v 1 ∉ L.lattice) :
      eval ![r 0 + v 0, L.weierstrassP (r 1 + v 1),
        L.derivWeierstrassP (r 1 + v 1), r 2 + v 2 + weierstrassZeta L (r 1 + v 1)]
          (extensionChartNormalize 0 Q) = 0 := by
    let z := r 1 + v 1
    let u := r 2 + v 2
    have he := translated_block_scaling Q n hQ
      ![1, r 0 + v 0, 1, L.weierstrassP z, L.derivWeierstrassP z,
        u + weierstrassZeta L z,
        L.derivWeierstrassP z * (u + weierstrassZeta L z) + 2 * L.weierstrassP z ^ 2]
      (D.sigma z ^ 3)
    rw [← translated_normalize_eval] at he
    have heq : eval ![1, r 0 + v 0, S 0 z, S 1 z, S 2 z,
        S 3 z + u * S 0 z, S 4 z + u * S 2 z] Q =
        (D.sigma z ^ 3) ^ n *
          eval ![r 0 + v 0, L.weierstrassP z, L.derivWeierstrassP z,
            u + weierstrassZeta L z] (extensionChartNormalize 0 Q) := by
      rw [← he]
      apply congrArg (fun w : Fin 7 → ℂ => eval w Q)
      funext i
      fin_cases i <;> simp [hS_value z hz] <;> ring
    rw [hvanish v hv] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero n (pow_ne_zero 3 (hσ z hz)))
  rcases affine_coset_polynomial_profile L V r (extensionChartNormalize 0 Q)
      hproper haffine with ht | hz
  · refine ⟨X 0, ⟨L.ω₁ / 2, L.ω₁_div_two_notMem_lattice, ?_⟩, ?_⟩
    · simpa using div_ne_zero (L.indep.ne_zero (0 : Fin 2)) (by norm_num : (2 : ℂ) ≠ 0)
    · intro v hv _
      simpa using ht v hv
  · refine ⟨1, ⟨L.ω₁ / 2, L.ω₁_div_two_notMem_lattice, by simp⟩, ?_⟩
    intro v hv hreg
    exact (hreg (by rw [hz v hv]; exact L.lattice.zero_mem)).elim
