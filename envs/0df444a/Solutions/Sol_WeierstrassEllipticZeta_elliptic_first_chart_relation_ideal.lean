-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_first_chart_relation_ideal
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T21:44:42.583519+00:00
-- url     : https://prove2.me/submissions/555909d0-cd9d-4bb2-bc18-1563692ad3c7

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
import Definitions.Def_WeierstrassEllipticZeta_FirstCubicChartBase
import Mathlib.Tactic


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
open MvPolynomial Filter
open scoped Topology
namespace WeierstrassEllipticZeta

private lemma wp_regular_image_infinite (L : PeriodPair) :
    (L.weierstrassP '' (L.lattice : Set ℂ)ᶜ).Infinite := by
  intro hfinite
  have hpole : meromorphicOrderAt L.weierstrassP 0 < 0 := by
    rw [L.order_weierstrassP 0 L.lattice.zero_mem]
    exact WithTop.coe_lt_coe.mpr (by decide)
  have hout := (tendsto_cobounded_of_meromorphicOrderAt_neg hpole)
    hfinite.isBounded
  have hregular : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ L.lattice := by
    have hnhds : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hw0
    exact fun hwL => hw ⟨hwL, hw0⟩
  obtain ⟨w, hw, hwout⟩ := (hregular.and hout).exists
  exact hwout ⟨w, hw, rfl⟩

private def omitY : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  aeval ![X 0, X 1, X 3]

private def cubicRHS (g₂ g₃ : ℂ) : MvPolynomial (Fin 3) ℂ :=
  C 4 * X 1 ^ 3 - C g₂ * X 1 - C g₃

private lemma omitY_eval (A : MvPolynomial (Fin 3) ℂ) (t x y u : ℂ) :
    eval ![t, x, y, u] (omitY A) = eval ![t, x, u] A := by
  change (aeval ![t, x, y, u]) ((aeval ![X 0, X 1, X 3]) A) =
    (aeval ![t, x, u]) A
  rw [comp_aeval_apply]
  apply congrArg (fun f : Fin 3 → ℂ => (aeval f) A)
  funext i
  fin_cases i <;> simp

private lemma cubic_normal_form (g₂ g₃ : ℂ) (P : MvPolynomial (Fin 4) ℂ) :
    ∃ A B : MvPolynomial (Fin 3) ℂ, ∃ H : MvPolynomial (Fin 4) ℂ,
      P = omitY A + X 2 * omitY B + extensionChartCubic g₂ g₃ 0 * H := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 0, 0, by simp [omitY]⟩
  | add P Q hP hQ =>
    obtain ⟨A, B, H, rfl⟩ := hP
    obtain ⟨A', B', H', rfl⟩ := hQ
    exact ⟨A + A', B + B', H + H', by simp only [map_add]; ring⟩
  | mul_X P i hP =>
    obtain ⟨A, B, H, rfl⟩ := hP
    fin_cases i
    · refine ⟨A * X 0, B * X 0, H * X 0, ?_⟩
      simp [omitY]
      ring
    · refine ⟨A * X 1, B * X 1, H * X 1, ?_⟩
      simp [omitY]
      ring
    · refine ⟨cubicRHS g₂ g₃ * B, A, omitY B + H * X 2, ?_⟩
      simp [omitY, cubicRHS, extensionChartCubic]
      ring
    · refine ⟨A * X 2, B * X 2, H * X 3, ?_⟩
      simp [omitY]
      ring

private lemma polynomial_zero_on_regular_fibres (L : PeriodPair)
    (A : MvPolynomial (Fin 3) ℂ)
    (hA : ∀ z, z ∉ L.lattice → ∀ t u : ℂ, eval ![t, L.weierstrassP z, u] A = 0) :
    A = 0 := by
  classical
  let s : Fin 3 → Set ℂ := ![Set.univ, L.weierstrassP '' (L.lattice : Set ℂ)ᶜ, Set.univ]
  have hs : ∀ i, (s i).Infinite := by
    intro i
    fin_cases i
    · exact Set.infinite_univ
    · exact wp_regular_image_infinite L
    · exact Set.infinite_univ
  apply funext_set s hs
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hx 1 (Set.mem_univ _)
  have he := hA z hz (x 0) (x 2)
  have hxvec : ![x 0, x 1, x 2] = x := by ext i; fin_cases i <;> rfl
  simpa only [hzx, hxvec, map_zero] using he

/-- The only polynomial relation on the regular elliptic-zeta orbit is the
Weierstrass cubic, despite the extra two additive coordinates. -/
theorem regular_orbit_relation_iff_cubic (L : PeriodPair)
    (P : MvPolynomial (Fin 4) ℂ) :
    (∀ z : ℂ, z ∉ L.lattice →
      eval ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z] P = 0) ↔
      P ∈ Ideal.span {extensionChartCubic L.g₂ L.g₃ 0} := by
  classical
  constructor
  · intro hP
    have hs := linear_direction_polynomial_saturation L 1 0 one_ne_zero P (by
      simpa using hP)
    obtain ⟨A, B, H, heq⟩ := cubic_normal_form L.g₂ L.g₃ P
    have hAB (z : ℂ) (hz : z ∉ L.lattice) (t u : ℂ) :
        eval ![t, L.weierstrassP z, u] A = 0 ∧
        (L.derivWeierstrassP z) * eval ![t, L.weierstrassP z, u] B = 0 := by
      have hm : -z ∉ L.lattice := fun h => hz (by simpa using L.lattice.neg_mem h)
      have hc : eval ![t, L.weierstrassP z, L.derivWeierstrassP z, u]
          (extensionChartCubic L.g₂ L.g₃ 0) = 0 := by
        simp [extensionChartCubic, L.derivWeierstrassP_sq z hz]
        ring
      have hc' : eval ![t, L.weierstrassP z, -L.derivWeierstrassP z, u]
          (extensionChartCubic L.g₂ L.g₃ 0) = 0 := by
        simp [extensionChartCubic, L.derivWeierstrassP_sq z hz]
        ring
      have hp := hs z hz t u
      have hn := hs (-z) hm t u
      rw [heq] at hp hn
      simp only [L.weierstrassP_neg, L.derivWeierstrassP_neg] at hn
      simp only [map_add, map_mul, eval_X, omitY_eval, hc, hc', zero_mul, add_zero] at hp hn
      change eval ![t, L.weierstrassP z, u] A +
        L.derivWeierstrassP z * eval ![t, L.weierstrassP z, u] B = 0 at hp
      change eval ![t, L.weierstrassP z, u] A +
        -L.derivWeierstrassP z * eval ![t, L.weierstrassP z, u] B = 0 at hn
      constructor
      · linear_combination (hp + hn) / 2
      · linear_combination (hp - hn) / 2
    have hA : A = 0 := polynomial_zero_on_regular_fibres L A
      (fun z hz t u => (hAB z hz t u).1)
    have hFB : cubicRHS L.g₂ L.g₃ * B = 0 := by
      apply polynomial_zero_on_regular_fibres L
      intro z hz t u
      have hb := (hAB z hz t u).2
      simp only [map_mul]
      have hf : eval ![t, L.weierstrassP z, u] (cubicRHS L.g₂ L.g₃) =
          L.derivWeierstrassP z ^ 2 := by
        simp [cubicRHS, L.derivWeierstrassP_sq z hz]
      rw [hf, pow_two, mul_assoc, hb, mul_zero]
    have hF : cubicRHS L.g₂ L.g₃ ≠ 0 := by
      intro h
      have hc := congrArg (coeff (Finsupp.single (1 : Fin 3) 3)) h
      norm_num [cubicRHS, C_mul_X_pow_eq_monomial, C_mul_X_eq_monomial,
        coeff_monomial, coeff_C,
        show Finsupp.single (1 : Fin 3) 1 ≠ Finsupp.single 1 3 from fun h => by
          have hh := congrArg (fun f : Fin 3 →₀ ℕ => f 1) h
          norm_num at hh,
        show (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 1 3 from fun h => by
          have hh := congrArg (fun f : Fin 3 →₀ ℕ => f 1) h
          norm_num at hh] at hc
    have hB : B = 0 := (mul_eq_zero.mp hFB).resolve_left hF
    rw [heq, hA, hB, map_zero, mul_zero, add_zero, zero_add]
    exact Ideal.mul_mem_right H _ (Ideal.subset_span (Set.mem_singleton _))
  · intro hP z hz
    have hc : eval ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z]
        (extensionChartCubic L.g₂ L.g₃ 0) = 0 := by
      simp [extensionChartCubic, L.derivWeierstrassP_sq z hz]
      ring
    have hle : Ideal.span {extensionChartCubic L.g₂ L.g₃ 0} ≤
        RingHom.ker (eval ![z, L.weierstrassP z, L.derivWeierstrassP z,
          weierstrassZeta L z]) := by
      exact Ideal.span_le.mpr (by simpa only [Set.singleton_subset_iff, RingHom.mem_ker])
    exact hle hP

private lemma first_chart_cubic_relation
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    extensionChartCubic L.g₂ L.g₃ 0 ∈ extensionGlobalChartKernel S 0 := by
  have ha (j : Fin 5) (w : ℂ) : AnalyticAt ℂ (S j) w := hS j w trivial
  have heq : (fun w => S 2 w ^ 2 * S 0 w - 4 * S 1 w ^ 3 +
      L.g₂ * S 1 w * S 0 w ^ 2 + L.g₃ * S 0 w ^ 3) = (0 : ℂ → ℂ) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (show AnalyticOnNhd ℂ _ Set.univ from fun w _ => by fun_prop)
      (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
      (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with u hu
    have hc := L.derivWeierstrassP_sq u hu
    simp [hS_value u hu]
    linear_combination D.sigma u ^ 9 * hc
  simp only [extensionGlobalChartKernel, Submodule.mem_iInf, RingHom.mem_ker]
  intro z hz
  have hc : S 2 z ^ 2 * S 0 z - 4 * S 1 z ^ 3 +
      L.g₂ * S 1 z * S 0 z ^ 2 + L.g₃ * S 0 z ^ 3 = 0 := congrFun heq z
  have hz0 : S 0 z ≠ 0 := hz
  simp [extensionChartCoordinates, extensionChartCubic]
  field_simp
  linear_combination hc



end WeierstrassEllipticZeta

open TranscendenceTheory WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    extensionGlobalChartKernel S 0 = Ideal.span {extensionChartCubic L.g₂ L.g₃ 0} ∧
      ∀ (Q : MvPolynomial (Fin 7) ℂ) (c : Fin 2),
        extensionFirstCubicChartBaseIdeal L S Q c = extensionGlobalChartBaseIdeal S Q c := by
  classical
  have hkernel : extensionGlobalChartKernel S 0 =
      Ideal.span {extensionChartCubic L.g₂ L.g₃ 0} := by
    apply le_antisymm
    · intro P hP
      apply (regular_orbit_relation_iff_cubic L P).mp
      intro z hz
      have hsig : D.sigma z ≠ 0 := by
        intro h
        obtain ⟨j, hj⟩ := hS_ne z
        exact hj (by simp [hS_value z hz, h])
      have h0 : S 0 z ≠ 0 := by simpa [hS_value z hz] using pow_ne_zero 3 hsig
      have he : eval (extensionChartCoordinates S 0 z) P = 0 := by
        have hh := hP
        simp only [extensionGlobalChartKernel, Submodule.mem_iInf, RingHom.mem_ker] at hh
        exact hh z h0
      have hv : extensionChartCoordinates S 0 z =
          ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z] := by
        ext i
        fin_cases i <;> simp [extensionChartCoordinates, hS_value z hz, hsig]
      rwa [hv] at he
    · apply Ideal.span_le.mpr
      rintro f rfl
      exact first_chart_cubic_relation L D S hS hS_value
  refine ⟨hkernel, ?_⟩
  intro Q c
  by_cases hc : c = 0
  · simp [extensionFirstCubicChartBaseIdeal, extensionGlobalChartBaseIdeal, hc, hkernel]
  · simp [extensionFirstCubicChartBaseIdeal, extensionGlobalChartBaseIdeal, hc]
