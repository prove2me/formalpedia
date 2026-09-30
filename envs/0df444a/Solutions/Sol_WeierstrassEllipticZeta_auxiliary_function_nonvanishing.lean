-- Prove2me | solution 1 for WeierstrassEllipticZeta.auxiliary_function_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T12:56:50.215182+00:00
-- url     : https://prove2.me/submissions/91e62442-21fb-4565-89e3-5b3746c2b38b

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

private theorem p2m_period_quasiperiod_determinant_ne_zero (L : PeriodPair) :
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

private lemma p2m_wp_regular_image_infinite (L : PeriodPair) :
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

private lemma p2m_nat_period_mem (L : PeriodPair) (ω : ℂ)
    (hω : ω ∈ L.lattice) (n : ℕ) : (n : ℂ) * ω ∈ L.lattice := by
  simpa [nsmul_eq_mul] using L.lattice.nsmul_mem hω n

private lemma p2m_regular_add_period (L : PeriodPair) (z ω : ℂ)
    (hz : z ∉ L.lattice) (hω : ω ∈ L.lattice) : z + ω ∉ L.lattice := by
  intro h
  exact hz (by simpa only [add_sub_cancel_right] using L.lattice.sub_mem h hω)

private lemma p2m_zeta_add_nat_period (L : PeriodPair) (ω : ℂ)
    (hω : ω ∈ L.lattice) (z : ℂ) (hz : z ∉ L.lattice) (n : ℕ) :
    weierstrassZeta L (z + (n : ℂ) * ω) =
      weierstrassZeta L z + (n : ℂ) * zetaQuasiPeriod L ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show z + ((n + 1 : ℕ) : ℂ) * ω = (z + (n : ℂ) * ω) + ω by
      push_cast; ring]
    rw [weierstrassZeta_add_period L ω _ hω
      (p2m_regular_add_period L z _ hz (p2m_nat_period_mem L ω hω n)), ih]
    push_cast
    ring

private lemma p2m_polynomial_zero_of_periods (L : PeriodPair)
    (hdet : L.ω₁ * zetaQuasiPeriod L L.ω₂ - L.ω₂ * zetaQuasiPeriod L L.ω₁ ≠ 0)
    (P : MvPolynomial (Fin 3) ℂ)
    (hP : ∀ z : ℂ, z ∉ L.lattice →
      eval ![z, L.weierstrassP z, weierstrassZeta L z] P = 0) : P = 0 := by
  classical
  have horbit (z : ℂ) (hz : z ∉ L.lattice) (x y : ℂ) :
      eval ![x, L.weierstrassP z, y] P = 0 := by
    let f : Fin 3 → MvPolynomial (Fin 2) ℂ :=
      ![C z + C L.ω₁ * X 0 + C L.ω₂ * X 1,
        C (L.weierstrassP z),
        C (weierstrassZeta L z) + C (zetaQuasiPeriod L L.ω₁) * X 0 +
          C (zetaQuasiPeriod L L.ω₂) * X 1]
    let Q : MvPolynomial (Fin 2) ℂ := eval₂ C f P
    have hQeval (a b : ℂ) : eval ![a, b] Q =
        eval ![z + a * L.ω₁ + b * L.ω₂, L.weierstrassP z,
          weierstrassZeta L z + a * zetaQuasiPeriod L L.ω₁ +
            b * zetaQuasiPeriod L L.ω₂] P := by
      dsimp only [Q]
      rw [← eval_assoc]
      apply congrArg (fun u : Fin 3 → ℂ => eval u P)
      funext i
      fin_cases i <;> simp [f, mul_comm]
    have hQ : Q = 0 := by
      apply funext_set (fun _ : Fin 2 => Set.range (fun n : ℕ => (n : ℂ)))
        (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
      intro u hu
      obtain ⟨a, ha⟩ := hu 0 (Set.mem_univ _)
      obtain ⟨b, hb⟩ := hu 1 (Set.mem_univ _)
      have huval : u = ![(a : ℂ), (b : ℂ)] := by
        funext i
        fin_cases i
        · exact ha.symm
        · exact hb.symm
      rw [huval, hQeval, map_zero]
      have haL := p2m_nat_period_mem L L.ω₁ L.ω₁_mem_lattice a
      have hbL := p2m_nat_period_mem L L.ω₂ L.ω₂_mem_lattice b
      have hza := p2m_regular_add_period L z _ hz haL
      have hzab := p2m_regular_add_period L _ _ hza hbL
      have hwp : L.weierstrassP (z + (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) =
          L.weierstrassP z := by
        rw [L.weierstrassP_add_coe _ ⟨_, hbL⟩, L.weierstrassP_add_coe _ ⟨_, haL⟩]
      have hζ := p2m_zeta_add_nat_period L L.ω₂ L.ω₂_mem_lattice _ hza b
      rw [p2m_zeta_add_nat_period L L.ω₁ L.ω₁_mem_lattice z hz a] at hζ
      simpa only [hwp, hζ] using hP _ hzab
    let d := L.ω₁ * zetaQuasiPeriod L L.ω₂ - L.ω₂ * zetaQuasiPeriod L L.ω₁
    let a := ((x - z) * zetaQuasiPeriod L L.ω₂ - L.ω₂ * (y - weierstrassZeta L z)) / d
    let b := (L.ω₁ * (y - weierstrassZeta L z) - (x - z) * zetaQuasiPeriod L L.ω₁) / d
    have hx : z + a * L.ω₁ + b * L.ω₂ = x := by
      calc
        _ = z + ((x - z) * d) / d := by dsimp [a, b, d]; ring
        _ = x := by rw [mul_div_cancel_right₀ _ hdet]; ring
    have hy : weierstrassZeta L z + a * zetaQuasiPeriod L L.ω₁ +
        b * zetaQuasiPeriod L L.ω₂ = y := by
      calc
        _ = weierstrassZeta L z + ((y - weierstrassZeta L z) * d) / d := by
          dsimp [a, b, d]; ring
        _ = y := by rw [mul_div_cancel_right₀ _ hdet]; ring
    have hh := hQeval a b
    rw [hQ, map_zero, hx, hy] at hh
    exact hh.symm
  let s : Fin 3 → Set ℂ := ![Set.univ, L.weierstrassP '' (L.lattice : Set ℂ)ᶜ, Set.univ]
  have hs : ∀ i, (s i).Infinite := by
    intro i
    fin_cases i
    · exact Set.infinite_univ
    · exact p2m_wp_regular_image_infinite L
    · exact Set.infinite_univ
  apply funext_set s hs
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hx 1 (Set.mem_univ _)
  have he := horbit z hz (x 0) (x 2)
  have hxvec : ![x 0, x 1, x 2] = x := by ext i; fin_cases i <;> rfl
  simpa only [hzx, hxvec, map_zero] using he

private theorem p2m_auxiliary_function_nonvanishing_of_period_determinant
    (L : PeriodPair)
    (hdet : L.ω₁ * zetaQuasiPeriod L L.ω₂ - L.ω₂ * zetaQuasiPeriod L L.ω₁ ≠ 0)
    (m l : ℕ) (c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ)
    (hc : c ≠ 0) :
    ∃ z : ℂ, z ∉ L.lattice ∧
      (∑ i, c i * z ^ i.1.val * L.weierstrassP z ^ i.2.1.val *
        weierstrassZeta L z ^ i.2.2.val) ≠ 0 := by
  classical
  let exponent (i : Fin (m + 1) × Fin (l + 1) × Fin (l + 1)) : Fin 3 →₀ ℕ :=
    Finsupp.single 0 i.1.val + Finsupp.single 1 i.2.1.val + Finsupp.single 2 i.2.2.val
  have hinj : Function.Injective exponent := by
    intro a b h
    have h₀ := congrArg (fun d : Fin 3 →₀ ℕ => d 0) h
    have h₁ := congrArg (fun d : Fin 3 →₀ ℕ => d 1) h
    have h₂ := congrArg (fun d : Fin 3 →₀ ℕ => d 2) h
    simp [exponent, Fin.ext_iff] at h₀ h₁ h₂
    exact Prod.ext (Fin.ext h₀) (Prod.ext (Fin.ext h₁) (Fin.ext h₂))
  let P : MvPolynomial (Fin 3) ℂ :=
    ∑ i, C (c i) * X 0 ^ i.1.val * X 1 ^ i.2.1.val * X 2 ^ i.2.2.val
  have hcoeff (i) : coeff (exponent i) P = c i := by
    dsimp only [P]
    simp_rw [C_mul_X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, mul_one]
    rw [coeff_sum]
    simp only [coeff_monomial]
    change (∑ j, if exponent j = exponent i then c j else 0) = c i
    simp [hinj.eq_iff]
  by_contra hnone
  have hvalues (z : ℂ) (hz : z ∉ L.lattice) :
      eval ![z, L.weierstrassP z, weierstrassZeta L z] P = 0 := by
    have hzero : (∑ i, c i * z ^ i.1.val * L.weierstrassP z ^ i.2.1.val *
        weierstrassZeta L z ^ i.2.2.val) = 0 := by
      by_contra hne
      exact hnone ⟨z, hz, hne⟩
    simpa [P] using hzero
  have hzero := p2m_polynomial_zero_of_periods L hdet P hvalues
  apply hc
  funext i
  change c i = 0
  simpa only [hzero, coeff_zero] using (hcoeff i).symm

theorem solution
    (L : PeriodPair) (m l : ℕ)
    (c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ)
    (hc : c ≠ 0) :
    ∃ z : ℂ, z ∉ L.lattice ∧
      (∑ i, c i * z ^ i.1.val * L.weierstrassP z ^ i.2.1.val *
        weierstrassZeta L z ^ i.2.2.val) ≠ 0 :=
  p2m_auxiliary_function_nonvanishing_of_period_determinant L
    (p2m_period_quasiperiod_determinant_ne_zero L) m l c hc
