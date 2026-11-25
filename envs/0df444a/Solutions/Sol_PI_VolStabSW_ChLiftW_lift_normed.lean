-- Prove2me | solution 1 for PI.VolStabSW.ChLiftW.lift_normed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:51:02.848962+00:00
-- url     : https://prove2.me/submissions/4cde2995-84f6-4555-b0df-9b4663176352

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensChLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open PI PI.VolStabSW
open PI.VolStabSW.ChLiftW
namespace PI.VolStabSW.ChLiftW
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hne : ∀ x, χ x ≠ 0 := by
    intro x h
    have h1 := hadd x (-x)
    rw [add_neg_cancel, h0, h, zero_mul] at h1
    exact one_ne_zero h1
  have hpow : ∀ (k : ℕ) (y : W), χ ((k : ℝ) • y) = χ y ^ k := by
    intro k y
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ y : W, ‖y‖ ≤ δ → ‖χ y - 1‖ < 1 / 2 := by
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
    have h2 := h (x := y) (by rw [dist_zero_right]; linarith)
    rwa [h0, dist_eq_norm] at h2
  have hre : ∀ y : W, ‖y‖ ≤ δ → 0 < (χ y).re := by
    intro y hy
    have h1 := hball y hy
    have h2 : |(χ y - 1).re| ≤ ‖χ y - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_le.1 (h2.trans h1.le)).1
    linarith
  have harg : ∀ y : W, ‖y‖ ≤ δ → |Complex.arg (χ y)| < Real.pi / 2 := fun y hy =>
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre y hy))
  set L : W → ℂ := fun y => Complex.log (χ y) with hL
  have hL0 : L 0 = 0 := by simp [hL, h0]
  have hLadd : ∀ y z : W, ‖y‖ ≤ δ → ‖z‖ ≤ δ → L (y + z) = L y + L z := by
    intro y z hy hz
    simp only [hL]
    have h1 := abs_lt.1 (harg y hy)
    have h2 := abs_lt.1 (harg z hz)
    rw [hadd, Complex.log_mul (hne y) (hne z)]
    constructor <;> linarith [Real.pi_pos]
  have hLsmul : ∀ (k : ℕ) (y : W), (k : ℝ) * ‖y‖ ≤ δ → L ((k : ℝ) • y) = k * L y := by
    intro k y
    induction k with
    | zero => intro _; simp [hL0]
    | succ k ih =>
      intro hk
      have hy0 := norm_nonneg y
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast at hk
      have h1 : (k : ℝ) * ‖y‖ ≤ δ := by nlinarith
      have h2 : ‖y‖ ≤ δ := by nlinarith
      have h3 : ‖(k : ℝ) • y‖ ≤ δ := by rw [norm_smul, Real.norm_natCast]; exact h1
      rw [Nat.cast_succ, add_smul, one_smul, hLadd _ _ h3 h2, ih h1]
      push_cast
      ring
  have hkey : ∀ (a b : ℕ) (x : W), 0 < a → 0 < b → ‖x‖ ≤ a * δ → ‖x‖ ≤ b * δ →
      (a : ℂ) * L ((a : ℝ)⁻¹ • x) = (b : ℂ) * L ((b : ℝ)⁻¹ • x) := by
    intro a b x ha hb hxa hxb
    have ha' : (0 : ℝ) < a := Nat.cast_pos.2 ha
    have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
    have e1 : (b : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (a : ℝ)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      field_simp
    have e2 : (a : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (b : ℝ)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      field_simp
    have ny : ‖((a : ℝ) * b)⁻¹ • x‖ = ‖x‖ / (a * b) := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
      ring
    have hb1 : (b : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ := by
      rw [ny, show (b : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / a by field_simp, div_le_iff₀ ha']
      linarith
    have ha1 : (a : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ := by
      rw [ny, show (a : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / b by field_simp, div_le_iff₀ hb']
      linarith
    rw [← e1, ← e2, hLsmul b _ hb1, hLsmul a _ ha1]
    ring
  set N : W → ℕ := fun x => ⌈‖x‖ / δ⌉₊ + 1 with hN
  have hNpos : ∀ x, 0 < N x := fun x => Nat.succ_pos _
  have hNle : ∀ x, ‖x‖ ≤ (N x : ℝ) * δ := by
    intro x
    have h1 : ‖x‖ / δ ≤ ⌈‖x‖ / δ⌉₊ := Nat.le_ceil _
    have h2 : ‖x‖ ≤ (⌈‖x‖ / δ⌉₊ : ℝ) * δ := by rwa [div_le_iff₀ hδ] at h1
    simp only [hN]
    push_cast
    nlinarith
  set f : W → ℂ := fun x => (N x : ℂ) * L ((N x : ℝ)⁻¹ • x) with hf
  have hfM : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → f x = M * L ((M : ℝ)⁻¹ • x) :=
    fun M x hM hx => hkey (N x) M x (hNpos x) hM (hNle x) hx
  have hsmall : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → ‖(M : ℝ)⁻¹ • x‖ ≤ δ := by
    intro M x hM hx
    have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hM'.le, inv_mul_le_iff₀ hM']
    linarith
  have fadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    have hMpos : 0 < N x + N y := by have := hNpos x; omega
    have hcx : (N x : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast (by omega : N x ≤ N x + N y)
    have hcy : (N y : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast (by omega : N y ≤ N x + N y)
    have hx : ‖x‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := (hNle x).trans hcx
    have hy : ‖y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := (hNle y).trans hcy
    have hxy : ‖x + y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      have h1 := norm_add_le x y
      have h2 := hNle x
      have h3 := hNle y
      push_cast
      linarith
    rw [hfM _ (x + y) hMpos hxy, hfM _ x hMpos hx, hfM _ y hMpos hy, smul_add,
      hLadd _ _ (hsmall _ x hMpos hx) (hsmall _ y hMpos hy), mul_add]
  have fexp : ∀ x, χ x = Complex.exp (f x) := by
    intro x
    show χ x = Complex.exp ((N x : ℂ) * Complex.log (χ ((N x : ℝ)⁻¹ • x)))
    rw [Complex.exp_nat_mul, Complex.exp_log (hne _), ← hpow, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast (hNpos x).ne'), one_smul]
  have fcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x0
    have hMpos : 0 < N x0 + 1 := Nat.succ_pos _
    have hMr : ((N x0 + 1 : ℕ) : ℝ) = N x0 + 1 := by push_cast; ring
    have hx0 : ‖x0‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ := by
      rw [hMr]
      nlinarith [hNle x0]
    have heq : (fun x => ((N x0 + 1 : ℕ) : ℂ) * L (((N x0 + 1 : ℕ) : ℝ)⁻¹ • x)) =ᶠ[nhds x0] f := by
      filter_upwards [Metric.ball_mem_nhds x0 hδ] with x hx
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have h1 : ‖x‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ := by
        have h2 := norm_sub_norm_le x x0
        rw [hMr]
        nlinarith [hNle x0]
      exact (hfM _ x hMpos h1).symm
    refine ContinuousAt.congr ?_ heq
    apply ContinuousAt.mul continuousAt_const
    simp only [hL]
    apply ContinuousAt.clog
    · exact (hc.comp (continuous_const_smul _)).continuousAt
    · exact Complex.mem_slitPlane_iff.2 (Or.inl (hre _ (hsmall _ x0 hMpos hx0)))
  exact ⟨AddMonoidHom.mk' f fadd, fcont, fexp⟩
end PI.VolStabSW.ChLiftW
