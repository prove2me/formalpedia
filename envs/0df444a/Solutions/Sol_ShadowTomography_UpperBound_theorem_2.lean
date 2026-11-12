-- Prove2me | solution 1 for ShadowTomography.UpperBound.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T07:34:08.251641+00:00
-- url     : https://prove2.me/submissions/e8bf7e80-78e5-4d6a-b7f0-121caf72b984

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal
import Definitions.Def_ShadowTomography_UpperBound_seqAccept
import Theorems.Thm_ShadowTomography_UpperBound_refinement_protocol
set_option autoImplicit false

/-! ### Sketch S1: `theorem_2` from the refinement protocol `K0` (parameter arithmetic). -/

open scoped ComplexOrder MatrixOrder
open ShadowTomography.UpperBound

/-- `log x ≥ 1 - 1/c` once `x ≥ c > 0`. -/
lemma s1_log_lb (x c : ℝ) (hc : 0 < c) (hx : c ≤ x) : 1 - 1 / c ≤ Real.log x := by
  have hxpos : 0 < x := lt_of_lt_of_le hc hx
  have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hxpos)
  rw [Real.log_inv] at h1
  have h2 : x⁻¹ ≤ c⁻¹ := inv_anti₀ hc hx
  rw [one_div]; linarith

/-- A constant `A` beating its own logarithmic overhead. -/
lemma s1_exists_A (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 1 ≤ A ∧ C₀ * (8 + 4 * Real.log (4 * (C₀ * (A + 1) + 1))) ≤ A := by
  have h1 := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1 / (8 * C₀) from
    div_pos one_pos (by linarith))
  have h2 : ∀ᶠ A : ℝ in Filter.atTop, (1:ℝ) ≤ A := Filter.eventually_ge_atTop 1
  have h3 : ∀ᶠ A : ℝ in Filter.atTop,
      2 * (C₀ * (8 + 4 * Real.log (8 * (C₀ + 1)))) ≤ A :=
    Filter.eventually_ge_atTop _
  obtain ⟨A, hA1, hA2, hA3⟩ := (h1.and (h2.and h3)).exists
  refine ⟨A, hA2, ?_⟩
  have hApos : 0 < A := by linarith
  have hle : 4 * (C₀ * (A + 1) + 1) ≤ 8 * (C₀ + 1) * A := by nlinarith
  have hpos : 0 < 4 * (C₀ * (A + 1) + 1) := by nlinarith [mul_pos hC₀ hApos]
  have hlog : Real.log (4 * (C₀ * (A + 1) + 1)) ≤ Real.log (8 * (C₀ + 1)) + Real.log A := by
    rw [← Real.log_mul (by nlinarith) hApos.ne']
    exact Real.log_le_log hpos hle
  have hlogA : Real.log A ≤ 1 / (8 * C₀) * A := by
    simp only [Real.norm_eq_abs, id] at hA1
    rw [abs_of_pos hApos] at hA1
    exact (le_abs_self _).trans hA1
  have h4 : 4 * C₀ * Real.log A ≤ A / 2 := by
    have := mul_le_mul_of_nonneg_left hlogA (by linarith : (0:ℝ) ≤ 4 * C₀)
    have e : 4 * C₀ * (1 / (8 * C₀) * A) = A / 2 := by field_simp; ring
    linarith
  have h5 := mul_le_mul_of_nonneg_left hlog hC₀.le
  nlinarith

set_option maxHeartbeats 400000 in
/-- The arithmetic core: with `q, T, ℓ, v` within `1` of their thresholds, the `K0`
hypothesis on `q` holds and `T (q ℓ + v)` is below the Theorem 2 bound. -/
lemma s1_arith (C₀ A L a b lM : ℝ) (q T ℓ v : ℕ)
    (hC₀ : 0 < C₀) (hA1 : 1 ≤ A)
    (hA : C₀ * (8 + 4 * Real.log (4 * (C₀ * (A + 1) + 1))) ≤ A)
    (hL : 0.69 ≤ L) (ha : 2 ≤ a) (hb0 : 0 < b) (hb : 0.69 ≤ Real.log b) (hlM : 0.69 ≤ lM)
    (hX27 : 0.27 ≤ Real.log L + Real.log a) (hXle : Real.log L + Real.log a ≤ L * a)
    (hloglM : -0.45 ≤ Real.log lM)
    (hq1 : A * (Real.log L + Real.log a) * a ^ 2 ≤ q)
    (hq2 : (q : ℝ) ≤ A * (Real.log L + Real.log a) * a ^ 2 + 1)
    (hT1 : 1 ≤ T) (hT2 : (T : ℝ) ≤ C₀ * q * L * a + 1)
    (hℓ : (ℓ : ℝ) ≤ C₀ * lM ^ 4 * (1 + Real.log lM + Real.log (T * b)) + 1)
    (hv : (v : ℝ) ≤ C₀ * (1 + Real.log (T * b)) * a ^ 2 + 1) :
    C₀ * (1 + Real.log T) * a ^ 2 ≤ q ∧
    ((T * (q * ℓ + v) : ℕ) : ℝ) ≤
      (C₀ * (A + 1) + 1) * ((A + 1) * (C₀ * (2 * (1 + Real.log (4 * (C₀ * (A + 1) + 1))) + 4) + 32)
        + 64 * (C₀ * (2 * (1 + Real.log (4 * (C₀ * (A + 1) + 1))) + 8) + 4)) *
      (L * a) * ((Real.log L + Real.log a) * a ^ 2) ^ 2 * lM ^ 4 *
      (Real.log lM + (Real.log L + Real.log a) + Real.log b) := by
  set K := 4 * (C₀ * (A + 1) + 1) with hK
  set X := Real.log L + Real.log a with hX
  set Y := Real.log lM + X + Real.log b with hY
  set Λ := C₀ * (2 * (1 + Real.log K) + 4) + 32 with hΛ
  set V := C₀ * (2 * (1 + Real.log K) + 8) + 4 with hV
  have hLpos : 0 < L := by linarith
  have hapos : 0 < a := by linarith
  have hLa0 : 0 ≤ L * a := mul_nonneg hLpos.le hapos.le
  have hX0 : 0 ≤ X := by linarith
  have hY5 : 0.5 ≤ Y := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hXY : X ≤ Y := by linarith
  have hc1 : 0 < C₀ * (A + 1) + 1 := by nlinarith [mul_pos hC₀ (show (0:ℝ) < A + 1 by linarith)]
  have hK4 : 4 ≤ K := by rw [hK]; nlinarith [mul_pos hC₀ (show (0:ℝ) < A + 1 by linarith)]
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
  have hΛ0 : 0 ≤ Λ := by linarith [mul_nonneg hC₀.le hlogK]
  have hV0 : 0 ≤ V := by linarith [mul_nonneg hC₀.le hlogK]
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT1
  have ha2 : 4 ≤ a ^ 2 := by nlinarith
  have hLa : 1.38 ≤ L * a := by linarith [mul_le_mul hL ha (by norm_num) hLpos.le]
  have hXa2 : 1 ≤ X * a ^ 2 := by linarith [mul_le_mul hX27 ha2 (by norm_num) hX0]
  have hXa2La : 1 ≤ X * a ^ 2 * (L * a) := by
    linarith [mul_le_mul hXa2 hLa (by norm_num) (by linarith)]
  have hq3 : (q : ℝ) ≤ (A + 1) * (X * a ^ 2) := by linarith
  have hT3 : (T : ℝ) ≤ (C₀ * (A + 1) + 1) * (X * a ^ 2 * (L * a)) := by
    have h1 := mul_le_mul_of_nonneg_left hq3 (mul_nonneg hC₀.le hLa0)
    linarith
  have haLa : a ≤ 2 * (L * a) := by linarith [mul_le_mul_of_nonneg_right hL hapos.le]
  have hTK : (T : ℝ) ≤ K * (L * a) ^ 4 := by
    have h2 : a ^ 2 ≤ (2 * (L * a)) ^ 2 := pow_le_pow_left₀ hapos.le haLa 2
    have h3 : X * a ^ 2 ≤ (L * a) * (2 * (L * a)) ^ 2 :=
      mul_le_mul hXle h2 (by positivity) hLa0
    have h1 : X * a ^ 2 * (L * a) ≤ 4 * (L * a) ^ 4 := by
      linarith [mul_le_mul_of_nonneg_right h3 hLa0]
    calc (T:ℝ) ≤ (C₀ * (A + 1) + 1) * (X * a ^ 2 * (L * a)) := hT3
      _ ≤ (C₀ * (A + 1) + 1) * (4 * (L * a) ^ 4) := mul_le_mul_of_nonneg_left h1 hc1.le
      _ = K * (L * a) ^ 4 := by rw [hK]; ring
  have hXlog : X = Real.log (L * a) := by rw [hX, Real.log_mul hLpos.ne' hapos.ne']
  have hlogT : Real.log T ≤ Real.log K + 4 * X := by
    have hLapos : 0 < L * a := by linarith
    have e : Real.log (K * (L * a) ^ 4) = Real.log K + 4 * X := by
      rw [Real.log_mul (by linarith) (pow_pos hLapos 4).ne', Real.log_pow, hXlog]; push_cast; ring
    rw [← e]; exact Real.log_le_log hTpos hTK
  have hS : 1 + Real.log K ≤ 2 * Y * (1 + Real.log K) := by
    linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * Y - 1) (by linarith : (0:ℝ) ≤ 1 + Real.log K)]
  constructor
  · have h1 : 1 + Real.log K ≤ 4 * X * (1 + Real.log K) := by
      linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 4 * X - 1) (by linarith : (0:ℝ) ≤ 1 + Real.log K)]
    have h3 : C₀ * (1 + Real.log T) ≤ C₀ * (1 + Real.log K + 4 * X) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₀.le
    have h4 : C₀ * (1 + Real.log K + 4 * X) ≤ C₀ * (X * (8 + 4 * Real.log K)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₀.le
    have h5 := mul_le_mul_of_nonneg_right hA hX0
    have h2 : C₀ * (1 + Real.log T) ≤ A * X := by linarith
    calc C₀ * (1 + Real.log T) * a ^ 2 ≤ A * X * a ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ q := hq1
  have hlogTb : Real.log (T * b) = Real.log T + Real.log b := Real.log_mul hTpos.ne' hb0.ne'
  have hlM4 : 0.2 ≤ lM ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hlM 4
    norm_num at this; linarith
  have hℓ' : (ℓ : ℝ) ≤ Λ * lM ^ 4 * Y := by
    have h1 : 1 + Real.log lM + Real.log (T * b) ≤ (2 * (1 + Real.log K) + 4) * Y := by
      rw [hlogTb]; linarith
    have h2 : C₀ * lM ^ 4 * (1 + Real.log lM + Real.log (T * b)) ≤
        C₀ * lM ^ 4 * ((2 * (1 + Real.log K) + 4) * Y) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hC₀.le (by positivity))
    have h3 : 1 ≤ 32 * lM ^ 4 * Y := by
      linarith [mul_le_mul hlM4 hY5 (by norm_num) (by positivity)]
    calc (ℓ:ℝ) ≤ _ := hℓ
      _ ≤ C₀ * lM ^ 4 * ((2 * (1 + Real.log K) + 4) * Y) + 32 * lM ^ 4 * Y := by linarith
      _ = Λ * lM ^ 4 * Y := by rw [hΛ]; ring
  have hv' : (v : ℝ) ≤ V * a ^ 2 * Y := by
    have h1 : 1 + Real.log (T * b) ≤ (2 * (1 + Real.log K) + 8) * Y := by
      rw [hlogTb]; linarith
    have h2 : C₀ * (1 + Real.log (T * b)) * a ^ 2 ≤
        C₀ * ((2 * (1 + Real.log K) + 8) * Y) * a ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC₀.le) (by positivity)
    have h3 : 1 ≤ 4 * a ^ 2 * Y := by linarith [mul_le_mul ha2 hY5 (by norm_num) (by positivity)]
    calc (v:ℝ) ≤ _ := hv
      _ ≤ C₀ * ((2 * (1 + Real.log K) + 8) * Y) * a ^ 2 + 4 * a ^ 2 * Y := by linarith
      _ = V * a ^ 2 * Y := by rw [hV]; ring
  have hF0 : 0 ≤ (C₀ * (A + 1) + 1) * (X * a ^ 2 * (L * a)) :=
    mul_nonneg hc1.le (mul_nonneg (mul_nonneg hX0 (by positivity)) hLa0)
  have hqℓ : (q:ℝ) * ℓ ≤ ((A + 1) * (X * a ^ 2)) * (Λ * lM ^ 4 * Y) :=
    mul_le_mul hq3 hℓ' (by positivity) (mul_nonneg (by linarith) (mul_nonneg hX0 (by positivity)))
  have hsum : (q:ℝ) * ℓ + v ≤ ((A + 1) * (X * a ^ 2)) * (Λ * lM ^ 4 * Y) + V * a ^ 2 * Y :=
    add_le_add hqℓ hv'
  have hTq : (T:ℝ) * (q * ℓ + v) ≤ ((C₀ * (A + 1) + 1) * (X * a ^ 2 * (L * a))) *
      (((A + 1) * (X * a ^ 2)) * (Λ * lM ^ 4 * Y) + V * a ^ 2 * Y) :=
    mul_le_mul hT3 hsum (by positivity) hF0
  have h64 : 1 ≤ 64 * X * lM ^ 4 := by linarith [mul_le_mul hX27 hlM4 (by norm_num) hX0]
  have hkey : V * a ^ 2 * Y ≤ 64 * V * (X * a ^ 2) * lM ^ 4 * Y := by
    have h0 : 0 ≤ V * a ^ 2 * Y := mul_nonneg (mul_nonneg hV0 (by positivity)) hY0
    linarith [mul_le_mul_of_nonneg_left h64 h0]
  calc ((T * (q * ℓ + v) : ℕ) : ℝ) = (T:ℝ) * (q * ℓ + v) := by push_cast; ring
    _ ≤ _ := hTq
    _ ≤ ((C₀ * (A + 1) + 1) * (X * a ^ 2 * (L * a))) *
          (((A + 1) * (X * a ^ 2)) * (Λ * lM ^ 4 * Y) + 64 * V * (X * a ^ 2) * lM ^ 4 * Y) := by
        apply mul_le_mul_of_nonneg_left _ hF0; linarith
    _ = _ := by ring

/-- The degenerate dimensions `D ∈ {0, 1}`: no copies are needed. -/
lemma s1_small (D : ℕ) (hD : D < 2) (M : ℕ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (E : Fin M → Matrix (Fin D) (Fin D) ℂ) (hE : ∀ i, IsEffect (E i)) :
    ∃ (Ω : Type) (_ : Fintype Ω) (P : POVM Ω (Fin 0 → Fin D)) (b : Ω → Fin M → ℝ),
      (∀ ω i, b ω i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ ρ : Matrix (Fin D) (Fin D) ℂ, WildeQIT.IsDensityOperator ρ →
        1 - δ ≤ P.prob (tensorPow ρ 0)
          (fun ω => ∀ i, |b ω i - ((E i) * ρ).trace.re| ≤ ε) := by
  interval_cases D
  · refine ⟨Unit, inferInstance, ⟨fun _ => 1, fun _ => Matrix.PosSemidef.one, by simp⟩,
      fun _ _ => 0, by intros; simp, ?_⟩
    intro ρ hρ
    exfalso
    have := hρ.2
    simp [Matrix.trace] at this
  · refine ⟨Unit, inferInstance, ⟨fun _ => 1, fun _ => Matrix.PosSemidef.one, by simp⟩,
      fun _ i => (E i 0 0).re, ?_, ?_⟩
    · intro _ i
      have h1 : (0:ℂ) ≤ E i 0 0 := (hE i).1.diag_nonneg
      have h2 : (0:ℂ) ≤ (1 - E i) 0 0 := (hE i).2.diag_nonneg
      simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h2
      have h1' := (Complex.le_def.1 h1).1
      have h2' := (Complex.le_def.1 h2).1
      simp only [Complex.zero_re, Complex.sub_re, Complex.one_re] at h1' h2'
      exact ⟨h1', by linarith⟩
    · intro ρ hρ
      have hρ00 : ρ 0 0 = 1 := by
        have := hρ.2
        simpa [Matrix.trace_fin_one] using this
      have hev : ∀ i, |(E i 0 0).re - ((E i) * ρ).trace.re| ≤ ε := by
        intro i
        simp [Matrix.trace_fin_one, Matrix.mul_apply, hρ00]
        exact hε.le
      simp only [POVM.prob]
      rw [Finset.filter_true_of_mem (fun ω _ => hev)]
      simp [Matrix.trace, tensorPow]
      linarith

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D M : ℕ) (ε δ : ℝ), 2 ≤ M → 0 < ε → ε ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        ∃ k : ℕ, (k : ℝ) ≤ C * (Real.log D / ε) *
            ((Real.log (Real.log D) + Real.log (1 / ε)) / ε ^ 2) ^ 2 * Real.log M ^ 4 *
            (Real.log (Real.log M) + Real.log (Real.log D) + Real.log (1 / ε) +
              Real.log (1 / δ)) ∧
          ∀ E : Fin M → Matrix (Fin D) (Fin D) ℂ, (∀ i, IsEffect (E i)) →
            ∃ (Ω : Type) (_ : Fintype Ω) (P : POVM Ω (Fin k → Fin D)) (b : Ω → Fin M → ℝ),
              (∀ ω i, b ω i ∈ Set.Icc (0 : ℝ) 1) ∧
              ∀ ρ : Matrix (Fin D) (Fin D) ℂ, WildeQIT.IsDensityOperator ρ →
                1 - δ ≤ P.prob (tensorPow ρ k)
                  (fun ω => ∀ i, |b ω i - ((E i) * ρ).trace.re| ≤ ε) := by
  obtain ⟨C₀, hC₀, hK0⟩ := ShadowTomography.UpperBound.refinement_protocol
  obtain ⟨A, hA1, hA⟩ := s1_exists_A C₀ hC₀
  have hc1 : 0 < C₀ * (A + 1) + 1 := by nlinarith [mul_pos hC₀ (show (0:ℝ) < A + 1 by linarith)]
  have hlogK : 0 ≤ Real.log (4 * (C₀ * (A + 1) + 1)) :=
    Real.log_nonneg (by nlinarith [mul_pos hC₀ (show (0:ℝ) < A + 1 by linarith)])
  refine ⟨(C₀ * (A + 1) + 1) *
      ((A + 1) * (C₀ * (2 * (1 + Real.log (4 * (C₀ * (A + 1) + 1))) + 4) + 32)
        + 64 * (C₀ * (2 * (1 + Real.log (4 * (C₀ * (A + 1) + 1))) + 8) + 4)), ?_, ?_⟩
  · apply mul_pos hc1
    have h1 : 0 ≤ C₀ * (2 * (1 + Real.log (4 * (C₀ * (A + 1) + 1))) + 4) :=
      mul_nonneg hC₀.le (by linarith)
    have h2 : 0 ≤ C₀ * (2 * (1 + Real.log (4 * (C₀ * (A + 1) + 1))) + 8) :=
      mul_nonneg hC₀.le (by linarith)
    nlinarith
  intro D M ε δ hM hε hε2 hδ hδ2
  rcases Nat.lt_or_ge D 2 with hD | hD
  · refine ⟨0, ?_, fun E hE => s1_small D hD M ε δ hε hδ E hE⟩
    have h0 : Real.log (D : ℝ) = 0 := by interval_cases D <;> simp
    rw [h0]; simp
  have hlog2 := Real.log_two_gt_d9
  have hDr : (2:ℝ) ≤ D := by exact_mod_cast hD
  have hMr : (2:ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨L, hLd⟩ : ∃ L : ℝ, L = Real.log D := ⟨_, rfl⟩
  obtain ⟨lM, hlMd⟩ : ∃ x : ℝ, x = Real.log M := ⟨_, rfl⟩
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = 1 / ε := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = 1 / δ := ⟨_, rfl⟩
  have hL : 0.69 ≤ L := by rw [hLd]; have := Real.log_le_log (by norm_num) hDr; linarith
  have hlM : 0.69 ≤ lM := by rw [hlMd]; have := Real.log_le_log (by norm_num) hMr; linarith
  have ha : 2 ≤ a := by rw [had, le_div_iff₀ hε]; linarith
  have hb2 : 2 ≤ b := by rw [hbd, le_div_iff₀ hδ]; linarith
  have hb0 : 0 < b := by linarith
  have hb : 0.69 ≤ Real.log b := by have := Real.log_le_log (by norm_num) hb2; linarith
  have hLpos : 0 < L := by linarith
  have hapos : 0 < a := by linarith
  have hX27 : 0.27 ≤ Real.log L + Real.log a := by
    rw [← Real.log_mul hLpos.ne' hapos.ne']
    have h := s1_log_lb (L * a) 1.38 (by norm_num)
      (by nlinarith [mul_le_mul hL ha (by norm_num) hLpos.le])
    norm_num at h; linarith
  have hXle : Real.log L + Real.log a ≤ L * a := by
    rw [← Real.log_mul hLpos.ne' hapos.ne']
    linarith [Real.log_le_sub_one_of_pos (mul_pos hLpos hapos)]
  have hloglM : -0.45 ≤ Real.log lM := by
    have h := s1_log_lb lM 0.69 (by norm_num) hlM
    norm_num at h; linarith
  have hXa : 0 < A * (Real.log L + Real.log a) * a ^ 2 :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  obtain ⟨q, hqd⟩ : ∃ q : ℕ, q = ⌈A * (Real.log L + Real.log a) * a ^ 2⌉₊ := ⟨_, rfl⟩
  have hq1 : A * (Real.log L + Real.log a) * a ^ 2 ≤ q := by rw [hqd]; exact Nat.le_ceil _
  have hq2 : (q:ℝ) ≤ A * (Real.log L + Real.log a) * a ^ 2 + 1 := by
    rw [hqd]; exact (Nat.ceil_lt_add_one hXa.le).le
  have hqpos : (0:ℝ) < q := lt_of_lt_of_le hXa hq1
  have hTa : 0 < C₀ * q * L * a := mul_pos (mul_pos (mul_pos hC₀ hqpos) hLpos) hapos
  obtain ⟨T, hTd⟩ : ∃ T : ℕ, T = ⌈C₀ * q * L * a⌉₊ := ⟨_, rfl⟩
  have hT1' : C₀ * q * L * a ≤ T := by rw [hTd]; exact Nat.le_ceil _
  have hT2 : (T:ℝ) ≤ C₀ * q * L * a + 1 := by rw [hTd]; exact (Nat.ceil_lt_add_one hTa.le).le
  have hT1 : 1 ≤ T := by rw [hTd]; exact Nat.ceil_pos.2 hTa
  have hT1r : (1:ℝ) ≤ T := by exact_mod_cast hT1
  have hlogTb0 : 0 ≤ Real.log (T * b) := Real.log_nonneg (by nlinarith)
  have hS0 : 0 ≤ C₀ * lM ^ 4 * (1 + Real.log lM + Real.log (T * b)) :=
    mul_nonneg (mul_nonneg hC₀.le (by positivity)) (by linarith)
  have hv0 : 0 ≤ C₀ * (1 + Real.log (T * b)) * a ^ 2 :=
    mul_nonneg (mul_nonneg hC₀.le (by linarith)) (by positivity)
  obtain ⟨ℓ, hℓd⟩ : ∃ ℓ : ℕ, ℓ = ⌈C₀ * lM ^ 4 * (1 + Real.log lM + Real.log (T * b))⌉₊ :=
    ⟨_, rfl⟩
  obtain ⟨v, hvd⟩ : ∃ v : ℕ, v = ⌈C₀ * (1 + Real.log (T * b)) * a ^ 2⌉₊ := ⟨_, rfl⟩
  have hℓ2 : (ℓ:ℝ) ≤ C₀ * lM ^ 4 * (1 + Real.log lM + Real.log (T * b)) + 1 := by
    rw [hℓd]; exact (Nat.ceil_lt_add_one hS0).le
  have hv2 : (v:ℝ) ≤ C₀ * (1 + Real.log (T * b)) * a ^ 2 + 1 := by
    rw [hvd]; exact (Nat.ceil_lt_add_one hv0).le
  obtain ⟨hqK, hbound⟩ := s1_arith C₀ A L a b lM q T ℓ v hC₀ hA1 hA hL ha hb0 hb hlM hX27
    hXle hloglM hq1 hq2 hT1 hT2 hℓ2 hv2
  have hTb : (T:ℝ) / δ = T * b := by rw [hbd]; ring
  have hK := hK0 D M ε δ q ℓ v T hD hM hε hε2 hδ hδ2
    (by
      have e : C₀ * (1 + Real.log T) / ε ^ 2 = C₀ * (1 + Real.log T) * a ^ 2 := by
        rw [had]; ring
      rw [e]; exact hqK)
    (by
      have e : C₀ * q * Real.log D / ε = C₀ * q * L * a := by rw [hLd, had]; ring
      rw [e]; exact hT1')
    (by rw [← hlMd, hTb, hℓd]; exact Nat.le_ceil _)
    (by
      have e : C₀ * (1 + Real.log (T / δ)) / ε ^ 2 = C₀ * (1 + Real.log (T * b)) * a ^ 2 := by
        rw [hTb, had]; ring
      rw [e, hvd]; exact Nat.le_ceil _)
  refine ⟨T * (q * ℓ + v), le_of_le_of_eq hbound ?_, hK⟩
  rw [hLd, hlMd, had, hbd]; ring
