-- Prove2me | solution 1 for TeschlQM.Shared.essentialSpectrum_exists_weyl_sequence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:45:22.831542+00:00
-- url     : https://prove2.me/submissions/7e9bc715-f725-4491-b230-f105d4ed99dc

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate

/-! D2 (abstract Weyl criterion) pieces: bridge between `A` and its resolvent `R` at a real point `t`. -/

namespace HVZD2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma res_symm (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (t : ℝ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) (x y : H) :
    ⟪R x, y⟫_ℂ = ⟪x, R y⟫_ℂ := by
  obtain ⟨hx, ex⟩ := hR.1 x
  obtain ⟨hy, ey⟩ := hR.1 y
  have hs : ⟪(R x : H), A ⟨R y, hy⟩⟫_ℂ = ⟪A ⟨R x, hx⟩, R y⟫_ℂ := hA.2 ⟨R x, hx⟩ ⟨R y, hy⟩
  calc ⟪R x, y⟫_ℂ = ⟪R x, A ⟨R y, hy⟩ - (t : ℂ) • R y⟫_ℂ := by rw [ey]
    _ = ⟪A ⟨R x, hx⟩ - (t : ℂ) • R x, R y⟫_ℂ := by
      rw [inner_sub_right, inner_smul_right, inner_sub_left, inner_smul_left, Complex.conj_ofReal, hs]
    _ = ⟪x, R y⟫_ℂ := by rw [ex]

lemma res_isSelfAdjoint (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (t : ℝ)
    (R : H →L[ℂ] H) (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) : IsSelfAdjoint R :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 (fun x y => res_symm A hA t R hR x y)

lemma mem_resolvent_of_not_mem (A : H →ₗ.[ℂ] H) (t : ℝ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) (z : ℂ) (hzt : z ≠ t)
    (hμ : (z - t)⁻¹ ∉ spectrum ℂ R) : z ∈ TeschlQM.Shared.resolventSet A := by
  rw [spectrum.mem_iff, not_not] at hμ
  have hc : z - (t : ℂ) ≠ 0 := sub_ne_zero.mpr hzt
  have hS : IsUnit ((1 : H →L[ℂ] H) - (z - t) • R) := by
    have : (1 : H →L[ℂ] H) - (z - t) • R =
        (z - t) • (algebraMap ℂ (H →L[ℂ] H) (z - t)⁻¹ - R) := by
      rw [smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [this, Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr hc).map _).mul hμ
  set S : H →L[ℂ] H := (1 : H →L[ℂ] H) - (z - t) • R with hSdef
  set U : H →L[ℂ] H := ↑(hS.unit⁻¹) with hU
  have hSU : S * U = 1 := hS.mul_val_inv
  have hUS : U * S = 1 := hS.val_inv_mul
  have key : ∀ v : H, U v - (z - t) • R (U v) = v := by
    intro v
    have := congrArg (fun T : H →L[ℂ] H => T v) hSU
    simpa [hSdef] using this
  have key2 : ∀ v : H, U (v - (z - t) • R v) = v := by
    intro v
    have := congrArg (fun T : H →L[ℂ] H => T v) hUS
    simpa [hSdef] using this
  refine ⟨R * U, fun φ => ?_, fun ψ => ?_⟩
  · obtain ⟨h, e⟩ := hR.1 (U φ)
    refine ⟨h, ?_⟩
    calc A ⟨(R * U) φ, h⟩ - z • (R * U) φ
        = (A ⟨R (U φ), h⟩ - (t : ℂ) • R (U φ)) - (z - t) • R (U φ) := by
          rw [sub_smul]; show A ⟨R (U φ), h⟩ - z • R (U φ) = _; abel
      _ = U φ - (z - t) • R (U φ) := by rw [e]
      _ = φ := key φ
  · set w : H := A ψ - (t : ℂ) • (ψ : H) with hw
    have hRw : R w = ψ := hR.2 ψ
    have : A ψ - z • (ψ : H) = w - (z - t) • R w := by
      rw [hRw, hw, sub_smul]; abel
    show R (U (A ψ - z • (ψ : H))) = ψ
    rw [this, key2, hRw]

lemma spec_real (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (t : ℝ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) (z : ℂ)
    (hz : z ∉ TeschlQM.Shared.resolventSet A) :
    z.im = 0 ∧ z ≠ t ∧ (z - t)⁻¹ ∈ spectrum ℂ R := by
  have hzt : z ≠ t := fun h => hz (h ▸ ⟨R, hR⟩)
  have hμ : (z - t)⁻¹ ∈ spectrum ℂ R := by
    by_contra h; exact hz (mem_resolvent_of_not_mem A t R hR z hzt h)
  refine ⟨?_, hzt, hμ⟩
  have hre := (res_isSelfAdjoint A hA t R hR).mem_spectrum_eq_re hμ
  have h1 : ((z - t)⁻¹).im = 0 := by rw [hre]; simp
  rw [Complex.inv_im, div_eq_zero_iff, neg_eq_zero] at h1
  rcases h1 with h1 | h1
  · simpa using h1
  · exact absurd (Complex.normSq_eq_zero.mp h1) (sub_ne_zero.mpr hzt)

open Filter Topology in
/-- transfer a Weyl sequence of the resolvent `R` at `μ = (z-t)⁻¹` to one of `A` at `z` -/
lemma transfer (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (t : ℝ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) (z : ℂ) (hzt : z ≠ t) (φ : ℕ → H)
    (hφ1 : ∀ n, ‖φ n‖ = 1) (hweak : ∀ v : H, Tendsto (fun n => ⟪v, φ n⟫_ℂ) atTop (𝓝 0))
    (hW : Tendsto (fun n => ‖R (φ n) - (z - t)⁻¹ • φ n‖) atTop (𝓝 0)) :
    ∃ ψ : ℕ → A.domain, (∀ n, ‖(ψ n : H)‖ = 1) ∧
      (∀ v : H, Tendsto (fun n => ⟪v, (ψ n : H)⟫_ℂ) atTop (𝓝 0)) ∧
      Tendsto (fun n => ‖A (ψ n) - z • (ψ n : H)‖) atTop (𝓝 0) := by
  have hc : z - (t : ℂ) ≠ 0 := sub_ne_zero.mpr hzt
  set μ : ℂ := (z - t)⁻¹ with hμ
  have hμ0 : μ ≠ 0 := inv_ne_zero hc
  have hinj : ∀ v : H, R v = 0 → v = 0 := by
    intro v hv
    obtain ⟨h, e⟩ := hR.1 v
    have h0 : (⟨R v, h⟩ : A.domain) = 0 := Subtype.ext hv
    rw [h0, LinearPMap.map_zero, hv, smul_zero, sub_zero] at e
    exact e.symm
  have hRne : ∀ n, R (φ n) ≠ 0 := by
    intro n h
    have := hinj _ h
    have h1 := hφ1 n
    rw [this, norm_zero] at h1
    exact zero_ne_one h1
  have hnorm : Tendsto (fun n => ‖R (φ n)‖) atTop (𝓝 ‖μ‖) := by
    have hconst : ∀ n, ‖μ • φ n‖ = ‖μ‖ := fun n => by rw [norm_smul, hφ1, mul_one]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hW
    rw [← hconst n, Real.norm_eq_abs]
    exact abs_norm_sub_norm_le _ _
  have hinv : Tendsto (fun n => ‖R (φ n)‖⁻¹) atTop (𝓝 ‖μ‖⁻¹) :=
    hnorm.inv₀ (norm_ne_zero_iff.mpr hμ0)
  let ψ : ℕ → A.domain := fun n =>
    ((‖R (φ n)‖⁻¹ : ℝ) : ℂ) • (⟨R (φ n), (hR.1 (φ n)).1⟩ : A.domain)
  have hψc : ∀ n, (ψ n : H) = ((‖R (φ n)‖⁻¹ : ℝ) : ℂ) • R (φ n) := fun n => rfl
  refine ⟨ψ, fun n => ?_, fun v => ?_, ?_⟩
  · rw [hψc, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hRne n))]
  · have h1 : ∀ n, ⟪v, (ψ n : H)⟫_ℂ = ((‖R (φ n)‖⁻¹ : ℝ) : ℂ) * ⟪R v, φ n⟫_ℂ := by
      intro n; rw [hψc, inner_smul_right, res_symm A hA t R hR]
    simp_rw [h1]
    have := ((Complex.continuous_ofReal.tendsto _).comp hinv).mul (hweak (R v))
    simpa using this
  · have h2 : ∀ n, A (ψ n) - z • (ψ n : H) =
        (((‖R (φ n)‖⁻¹ : ℝ) : ℂ) * (-(z - t))) • (R (φ n) - μ • φ n) := by
      intro n
      obtain ⟨h, e⟩ := hR.1 (φ n)
      have hA' : A (ψ n) = ((‖R (φ n)‖⁻¹ : ℝ) : ℂ) • A ⟨R (φ n), h⟩ :=
        LinearPMap.map_smul _ _ _
      have e' : A ⟨R (φ n), h⟩ = φ n + (t : ℂ) • R (φ n) := sub_eq_iff_eq_add.mp e
      have hk : (-(z - t)) • (R (φ n) - μ • φ n) = φ n - (z - t) • R (φ n) := by
        rw [smul_sub, smul_smul, neg_mul, hμ, mul_inv_cancel₀ hc]
        simp only [neg_smul, one_smul]
        abel
      rw [hA', hψc, mul_smul, hk, smul_comm z, ← smul_sub]
      congr 1
      rw [e', sub_smul]; abel
    simp only [h2, norm_smul, norm_mul, norm_neg, Complex.norm_real, norm_inv, norm_norm]
    have := (hinv.mul_const ‖z - (t : ℂ)‖).mul hW
    simpa using this

end HVZD2



open scoped InnerProductSpace ComplexConjugate
open Filter Topology

/-! D2 (abstract Weyl criterion), generic bounded self-adjoint part (W4/W5). -/

namespace HVZW

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma orth_weak {φ : ℕ → H} (hφ : Orthonormal ℂ φ) (v : H) :
    Tendsto (fun n => ⟪v, φ n⟫_ℂ) atTop (𝓝 0) := by
  have h2 : Tendsto (fun n => ‖⟪φ n, v⟫_ℂ‖ ^ 2) atTop (𝓝 0) :=
    (hφ.inner_products_summable (x := v)).tendsto_atTop_zero
  have h3 : Tendsto (fun n => ‖⟪φ n, v⟫_ℂ‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
    exact this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact h3.congr (fun n => norm_inner_symm _ _)

/-- triangular bump at `c` of radius `r` -/
noncomputable def bump (c r : ℝ) (x : ℝ) : ℝ := max 0 (1 - |x - c| / r)

/-- plateau cutoff: `1` on `|x - c| ≤ r`, `0` beyond `2r` -/
noncomputable def cut (c r : ℝ) (x : ℝ) : ℝ := min 1 (max 0 (2 - |x - c| / r))

lemma bump_cont (c r : ℝ) : Continuous (bump c r) := by
  unfold bump; fun_prop

lemma cut_cont (c r : ℝ) : Continuous (cut c r) := by
  unfold cut; fun_prop

lemma bump_eq_zero {c r x : ℝ} (hr : 0 < r) (hx : r ≤ |x - c|) : bump c r x = 0 := by
  unfold bump
  have : 1 ≤ |x - c| / r := (le_div_iff₀ hr).2 (by linarith)
  exact max_eq_left (by linarith)

lemma bump_self (c r : ℝ) : bump c r c = 1 := by
  simp [bump]

lemma cut_mul_bump {c r : ℝ} (hr : 0 < r) (x : ℝ) : cut c r x * bump c r x = bump c r x := by
  by_cases hx : r ≤ |x - c|
  · rw [bump_eq_zero hr hx, mul_zero]
  · push_neg at hx
    have : 1 ≤ 2 - |x - c| / r := by
      have : |x - c| / r < 1 := (div_lt_one hr).2 hx
      linarith
    have hc : cut c r x = 1 := by
      unfold cut; rw [max_eq_right (by linarith), min_eq_left this]
    rw [hc, one_mul]

lemma cut_bound {c r μ : ℝ} (hr : 0 < r) (x : ℝ) :
    |x * cut c r x - μ * cut c r x| ≤ |c - μ| + 2 * r := by
  have h0 : 0 ≤ cut c r x := le_min zero_le_one (le_max_left _ _)
  have h1 : cut c r x ≤ 1 := min_le_left _ _
  rw [← sub_mul, abs_mul, abs_of_nonneg h0]
  by_cases hx : 2 * r ≤ |x - c|
  · have : cut c r x = 0 := by
      unfold cut
      have : 2 ≤ |x - c| / r := (le_div_iff₀ hr).2 (by linarith)
      rw [max_eq_left (by linarith), min_eq_right zero_le_one]
    rw [this, mul_zero]; positivity
  · push_neg at hx
    have : |x - μ| ≤ |c - μ| + 2 * r := by
      calc |x - μ| = |(x - c) + (c - μ)| := by ring_nf
        _ ≤ |x - c| + |c - μ| := abs_add_le _ _
        _ ≤ |c - μ| + 2 * r := by linarith
    calc |x - μ| * cut c r x ≤ |x - μ| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ _ := by linarith

variable (R : H →L[ℂ] H)

lemma cfc_symm (hR : IsSelfAdjoint R) (f : ℝ → ℝ) (u v : H) :
    ⟪cfc f R u, v⟫_ℂ = ⟪u, cfc f R v⟫_ℂ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (IsSelfAdjoint.cfc (f := f) (a := R))) u v

/-- residual of a bump vector -/
lemma bump_resid (hR : IsSelfAdjoint R) {c r : ℝ} (hr : 0 < r) (μ : ℝ) (w : H) :
    ‖R (cfc (bump c r) R w) - (μ : ℂ) • cfc (bump c r) R w‖ ≤
      (|c - μ| + 2 * r) * ‖cfc (bump c r) R w‖ := by
  have hb := bump_cont c r
  have hk := cut_cont c r
  set φ := cfc (bump c r) R w with hφ
  have hfix : cfc (cut c r) R φ = φ := by
    have : cfc (bump c r) R = cfc (cut c r) R * cfc (bump c r) R := by
      rw [← cfc_mul (cut c r) (bump c r) R]
      exact cfc_congr (fun x _ => (cut_mul_bump hr x).symm)
    rw [hφ]; conv_rhs => rw [this]
    rfl
  have hop : R (cfc (cut c r) R φ) - (μ : ℂ) • cfc (cut c r) R φ =
      cfc (fun x => x * cut c r x - μ * cut c r x) R φ := by
    rw [cfc_sub (fun x => x * cut c r x) (fun x => μ * cut c r x) R,
      cfc_mul (fun x => x) (cut c r) R, cfc_id' ℝ R, cfc_const_mul μ (cut c r) R]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply]
    rw [← Complex.coe_smul]
  rw [← hfix, hop, hfix]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  gcongr
  refine norm_cfc_le (by positivity) (fun x _ => ?_)
  rw [Real.norm_eq_abs]
  exact cut_bound hr x

lemma bump_ne_zero (hR : IsSelfAdjoint R) {c r : ℝ} (hc : c ∈ spectrum ℝ R) :
    cfc (bump c r) R ≠ 0 := by
  intro h
  have hb := bump_cont c r
  have := norm_apply_le_norm_cfc (bump c r) R hc
  rw [h, bump_self, norm_zero, norm_one] at this
  exact absurd this (by norm_num)

lemma bump_orth (hR : IsSelfAdjoint R) {c r c' r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (hd : r + r' ≤ |c - c'|) (w w' : H) :
    ⟪cfc (bump c r) R w, cfc (bump c' r') R w'⟫_ℂ = 0 := by
  have hb := bump_cont c r
  have hb' := bump_cont c' r'
  rw [cfc_symm R hR, ← ContinuousLinearMap.mul_apply, ← cfc_mul (bump c r) (bump c' r') R]
  have : cfc (fun x => bump c r x * bump c' r' x) R = cfc (0 : ℝ → ℝ) R := by
    refine cfc_congr (fun x _ => ?_)
    show bump c r x * bump c' r' x = 0
    by_cases h1 : r ≤ |x - c|
    · rw [bump_eq_zero hr h1, zero_mul]
    · have h2 : r' ≤ |x - c'| := by
        push_neg at h1
        have : |c - c'| ≤ |x - c| + |x - c'| := by
          calc |c - c'| = |(x - c') - (x - c)| := by ring_nf
            _ ≤ |x - c'| + |x - c| := abs_sub _ _
            _ = _ := add_comm _ _
        linarith
      rw [bump_eq_zero hr' h2, mul_zero]
  rw [this, cfc_zero, ContinuousLinearMap.zero_apply, inner_zero_right]

/-- W5: an isolated point of the spectrum of a bounded self-adjoint operator is an eigenvalue -/
lemma isolated_eigen (hR : IsSelfAdjoint R) {μ ε : ℝ} (hμ : μ ∈ spectrum ℝ R) (hε : 0 < ε)
    (hiso : ∀ x ∈ spectrum ℝ R, |x - μ| < ε → x = μ) :
    ∃ v : H, v ≠ 0 ∧ R v = (μ : ℂ) • v := by
  have hne := bump_ne_zero R hR (r := ε) hμ
  obtain ⟨w, hw⟩ : ∃ w, cfc (bump μ ε) R w ≠ 0 := by
    by_contra h; push_neg at h; exact hne (ContinuousLinearMap.ext h)
  refine ⟨_, hw, ?_⟩
  have h0 := bump_resid R hR hε μ w (c := μ)
  -- sharper: the residual vanishes since `(x - μ) * bump = 0` on the spectrum
  have hb := bump_cont μ ε
  have hz : cfc (fun x => x * bump μ ε x - μ * bump μ ε x) R = 0 := by
    rw [← cfc_zero ℝ R]
    refine cfc_congr (fun x hx => ?_)
    show x * bump μ ε x - μ * bump μ ε x = 0
    by_cases h : |x - μ| < ε
    · rw [hiso x hx h]; ring
    · push_neg at h; rw [bump_eq_zero hε h]; ring
  have hop : R (cfc (bump μ ε) R w) - (μ : ℂ) • cfc (bump μ ε) R w =
      cfc (fun x => x * bump μ ε x - μ * bump μ ε x) R w := by
    rw [cfc_sub (fun x => x * bump μ ε x) (fun x => μ * bump μ ε x) R,
      cfc_mul (fun x => x) (bump μ ε) R, cfc_id' ℝ R, cfc_const_mul μ (bump μ ε) R]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply]
    rw [← Complex.coe_smul]
  rw [hz, ContinuousLinearMap.zero_apply] at hop
  exact sub_eq_zero.mp hop

/-- W4: an accumulation point of the spectrum of a bounded self-adjoint operator carries an
orthonormal Weyl sequence (bump vectors with disjoint spectral supports). -/
lemma weyl_acc (hR : IsSelfAdjoint R) (μ : ℝ)
    (hacc : ∀ ε > 0, ∃ x ∈ spectrum ℝ R, x ≠ μ ∧ |x - μ| < ε) :
    ∃ φ : ℕ → H, Orthonormal ℂ φ ∧
      Tendsto (fun n => ‖R (φ n) - (μ : ℂ) • φ n‖) atTop (𝓝 0) := by
  have hacc' : ∀ ε : {ε : ℝ // 0 < ε}, ∃ x ∈ spectrum ℝ R, 0 < |x - μ| ∧ |x - μ| < ε.1 := by
    intro ε
    obtain ⟨x, hx, hne, hlt⟩ := hacc ε.1 ε.2
    exact ⟨x, hx, abs_pos.2 (sub_ne_zero.2 hne), hlt⟩
  choose G hGσ hGpos hGlt using hacc'
  let e : ℕ → {ε : ℝ // 0 < ε} := fun n =>
    Nat.rec ⟨1, one_pos⟩ (fun _ ε => ⟨|G ε - μ| / 3, by have := hGpos ε; positivity⟩) n
  set p : ℕ → ℝ := fun n => G (e n) with hp
  set δ : ℕ → ℝ := fun n => |p n - μ| with hδ
  have hδpos : ∀ n, 0 < δ n := fun n => hGpos (e n)
  have hδs : ∀ n, δ (n + 1) < δ n / 3 := fun n => hGlt (e (n + 1))
  have hδ0 : δ 0 < 1 := hGlt (e 0)
  have hδpow : ∀ n, δ n ≤ (1 / 3 : ℝ) ^ n := by
    intro n; induction n with
    | zero => simpa using hδ0.le
    | succ n ih =>
      rw [pow_succ]
      have := hδs n
      linarith
  have hanti : StrictAnti δ := strictAnti_nat_of_succ_lt (fun n => by
    have := hδs n; have := hδpos n; linarith)
  set r : ℕ → ℝ := fun n => δ n / 3 with hr
  have hrpos : ∀ n, 0 < r n := fun n => by have := hδpos n; simp only [hr]; positivity
  have sep : ∀ k j, k < j → r k + r j ≤ |p k - p j| := by
    intro k j hkj
    have h1 : δ j ≤ δ (k + 1) := hanti.antitone hkj
    have h2 := hδs k
    have h3 : δ k - δ j ≤ |p k - p j| := by
      have := abs_sub_abs_le_abs_sub (p k - μ) (p j - μ)
      simp only [hδ]
      calc |p k - μ| - |p j - μ| ≤ |(p k - μ) - (p j - μ)| := this
        _ = |p k - p j| := by ring_nf
    simp only [hr]
    have := hδpos j
    linarith
  have hw : ∀ n, ∃ w : H, cfc (bump (p n) (r n)) R w ≠ 0 := by
    intro n
    by_contra h; push_neg at h
    exact bump_ne_zero R hR (r := r n) (hGσ (e n)) (ContinuousLinearMap.ext h)
  choose w hw using hw
  let φ : ℕ → H := fun n =>
    cfc (bump (p n) (r n)) R (((‖cfc (bump (p n) (r n)) R (w n)‖⁻¹ : ℝ) : ℂ) • w n)
  have hφn : ∀ n, ‖φ n‖ = 1 := by
    intro n
    simp only [φ, map_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hw n))
  refine ⟨φ, ⟨hφn, fun i j hij => ?_⟩, ?_⟩
  · rcases lt_or_gt_of_ne hij with h | h
    · exact bump_orth R hR (hrpos i) (hrpos j) (sep i j h) _ _
    · have := sep j i h
      rw [abs_sub_comm, add_comm] at this
      exact bump_orth R hR (hrpos i) (hrpos j) this _ _
  · have hb : ∀ n, ‖R (φ n) - (μ : ℂ) • φ n‖ ≤ 5 / 3 * (1 / 3 : ℝ) ^ n := by
      intro n
      have := bump_resid R hR (hrpos n) μ
        (((‖cfc (bump (p n) (r n)) R (w n)‖⁻¹ : ℝ) : ℂ) • w n) (c := p n)
      refine this.trans ?_
      have h1 : ‖cfc (bump (p n) (r n)) R
          (((‖cfc (bump (p n) (r n)) R (w n)‖⁻¹ : ℝ) : ℂ) • w n)‖ = 1 := hφn n
      rw [h1, mul_one]
      have h2 : |p n - μ| = δ n := rfl
      rw [h2]
      have := hδpow n
      simp only [hr]
      linarith
    refine squeeze_zero (fun n => norm_nonneg _) hb ?_
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num)
      (by norm_num)).const_mul (5 / 3)
    simpa using this

end HVZW

namespace HVZD2b

open HVZD2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma eig_mem (A : H →ₗ.[ℂ] H) (t : ℝ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) (z : ℂ) (hzt : z ≠ t) (v : H)
    (hv : R v = (z - t)⁻¹ • v) : v ∈ TeschlQM.Shared.eigenspace A z := by
  obtain ⟨h, e⟩ := hR.1 v
  have hc : z - (t : ℂ) ≠ 0 := sub_ne_zero.mpr hzt
  have hvv : (z - t) • R v = v := by rw [hv, smul_smul, mul_inv_cancel₀ hc, one_smul]
  let x : A.domain := (z - t) • (⟨R v, h⟩ : A.domain)
  have hx : (x : H) = v := hvv
  refine Submodule.mem_map.2 ⟨x, ?_, hx⟩
  rw [LinearMap.mem_ker]
  show A x - z • (x : H) = 0
  have hAx : A x = (z - t) • A ⟨R v, h⟩ := LinearPMap.map_smul _ _ _
  have e' : A ⟨R v, h⟩ = v + (t : ℂ) • R v := sub_eq_iff_eq_add.mp e
  rw [hx, hAx, e', smul_add, smul_comm (z - t) (t : ℂ) (R v), hvv, ← add_smul, sub_add_cancel,
    sub_self]

lemma ortho_seq (V : Submodule ℂ H) (hV : ¬ FiniteDimensional ℂ V) :
    ∃ e : ℕ → H, Orthonormal ℂ e ∧ ∀ n, e n ∈ V := by
  let b := Module.Basis.ofVectorSpace ℂ V
  have hinf : Infinite (Module.Basis.ofVectorSpaceIndex ℂ V) := by
    by_contra h
    rw [not_infinite_iff_finite] at h
    exact hV (Module.Finite.of_basis b)
  let f : ℕ → V := fun n => b (Infinite.natEmbedding _ n)
  have hli : LinearIndependent ℂ f :=
    b.linearIndependent.comp _ (Infinite.natEmbedding _).injective
  obtain ⟨g, hgo⟩ : ∃ g : ℕ → V, Orthonormal ℂ g :=
    ⟨_, InnerProductSpace.gramSchmidtNormed_orthonormal hli⟩
  exact ⟨fun n => (g n : H), hgo.comp_linearIsometry V.subtypeₗᵢ, fun n => (g n).2⟩

lemma weyl_main (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (t : ℝ) (ht : (t : ℂ) ∈ TeschlQM.Shared.resolventSet A) (z : ℂ)
    (hz : z ∈ TeschlQM.Shared.essentialSpectrum A) :
    z.im = 0 ∧ ∃ ψ : ℕ → A.domain, (∀ n, ‖(ψ n : H)‖ = 1) ∧
      (∀ φ : H, Tendsto (fun n => inner ℂ φ (ψ n : H)) atTop (nhds 0)) ∧
      Tendsto (fun n => ‖A (ψ n) - z • (ψ n : H)‖) atTop (nhds 0) := by
  rw [TeschlQM.Shared.essentialSpectrum, Set.mem_diff] at hz
  obtain ⟨R, hR⟩ := ht
  obtain ⟨him, hzt, hμC⟩ := spec_real A hA t R hR z hz.1
  refine ⟨him, ?_⟩
  have hRsa := res_isSelfAdjoint A hA t R hR
  set μ : ℝ := (z.re - t)⁻¹ with hμ
  have hzre : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
  have hμc : (z - t)⁻¹ = (μ : ℂ) := by
    rw [hμ, Complex.ofReal_inv, Complex.ofReal_sub]
    congr 1
    exact congrArg (· - (t : ℂ)) hzre
  have hμR : μ ∈ spectrum ℝ R := by
    apply (spectrum.algebraMap_mem_iff ℂ).1
    simpa [hμc] using hμC
  by_cases hiso : ∃ ε > 0, ∀ x ∈ spectrum ℝ R, |x - μ| < ε → x = μ
  · obtain ⟨ε, hε, hiso⟩ := hiso
    by_cases hfin : FiniteDimensional ℂ (TeschlQM.Shared.eigenspace A z)
    · exfalso
      apply hz.2
      rw [TeschlQM.Shared.discreteSpectrum, Set.mem_setOf_eq]
      refine ⟨hz.1, ?_, ?_, hfin⟩
      · obtain ⟨v, hv0, hv⟩ := HVZW.isolated_eigen R hRsa hμR hε hiso
        intro hbot
        have : v ∈ TeschlQM.Shared.eigenspace A z :=
          eig_mem A t R hR z hzt v (by rw [hμc]; exact hv)
        rw [hbot, Submodule.mem_bot] at this
        exact hv0 this
      · have hcont : ContinuousAt (fun w : ℂ => (w - t)⁻¹) z :=
          ((continuous_id.sub continuous_const).continuousAt).inv₀ (sub_ne_zero.mpr hzt)
        obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont ε hε
        refine ⟨δ, hδ, fun w hw hwz => ?_⟩
        obtain ⟨wim, hwt, hwμ⟩ := spec_real A hA t R hR w hw
        have hwre : w = (w.re : ℂ) := Complex.ext rfl (by simp [wim])
        have hwc : (w - t)⁻¹ = (((w.re - t)⁻¹ : ℝ) : ℂ) := by
          rw [Complex.ofReal_inv, Complex.ofReal_sub]
          congr 1
          exact congrArg (· - (t : ℂ)) hwre
        have hmem : (w.re - t)⁻¹ ∈ spectrum ℝ R := by
          apply (spectrum.algebraMap_mem_iff ℂ).1
          simpa [hwc] using hwμ
        have hd : |(w.re - t)⁻¹ - μ| < ε := by
          have := hball (by rw [dist_eq_norm]; exact hwz)
          simp only [dist_eq_norm] at this
          rw [hwc, hμc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
          exact this
        have heq := hiso _ hmem hd
        have : (w - t)⁻¹ = (z - t)⁻¹ := by rw [hwc, hμc, heq]
        exact sub_left_injective (inv_injective this)
    · obtain ⟨e, he, heV⟩ := ortho_seq _ hfin
      have hx : ∀ n, ∃ x : A.domain, A x - z • (x : H) = 0 ∧ (x : H) = e n := by
        intro n
        obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 (heV n)
        exact ⟨x, LinearMap.mem_ker.1 hx, hxe⟩
      choose x hx0 hxe using hx
      refine ⟨x, fun n => by rw [hxe]; exact he.1 n, fun φ => ?_, ?_⟩
      · simp_rw [hxe]; exact HVZW.orth_weak he φ
      · simp_rw [hx0, norm_zero]; exact tendsto_const_nhds
  · push_neg at hiso
    have hacc : ∀ ε > 0, ∃ x ∈ spectrum ℝ R, x ≠ μ ∧ |x - μ| < ε := by
      intro ε hε
      obtain ⟨x, hx, hlt, hne⟩ := hiso ε hε
      exact ⟨x, hx, hne, hlt⟩
    obtain ⟨φ, hφ, hW⟩ := HVZW.weyl_acc R hRsa μ hacc
    exact transfer A hA t R hR z hzt φ hφ.1 (HVZW.orth_weak hφ) (by rw [hμc]; exact hW)

end HVZD2b

theorem solution {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (t : ℝ) (ht : (t : ℂ) ∈ TeschlQM.Shared.resolventSet A) (z : ℂ)
    (hz : z ∈ TeschlQM.Shared.essentialSpectrum A) :
    z.im = 0 ∧ ∃ ψ : ℕ → A.domain, (∀ n, ‖(ψ n : H)‖ = 1) ∧
      (∀ φ : H, Tendsto (fun n => inner ℂ φ (ψ n : H)) atTop (nhds 0)) ∧
      Tendsto (fun n => ‖A (ψ n) - z • (ψ n : H)‖) atTop (nhds 0) := by
  exact HVZD2b.weyl_main A hA t ht z hz
