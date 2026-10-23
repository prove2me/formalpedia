-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.weakCoherenceExpansions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:27:48.496988+00:00
-- url     : https://prove2.me/submissions/4dd61acd-a902-4a1c-8e79-2220fe3102fe

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

theorem X7_den (q y D : ℝ) (hD : 0 < D) (hq : 0 ≤ q) (hq2 : 16 * q ≤ D) (hy : |y| ≤ 2) :
    D / 2 ≤ D - 4 * q * y := by
  have : y ≤ 2 := (abs_le.mp hy).2
  nlinarith

theorem X7_popb (q x y D : ℝ) (hD : 0 < D) (hq : 0 ≤ q) (hq2 : 16 * q ≤ D) (hy : |y| ≤ 2) :
    |2 * q / (D - 4 * q * y) * x * y - 2 * q * x * y / D| ≤ 64 * |x| / D ^ 2 * q ^ 2 := by
  have hden := X7_den q y D hD hq hq2 hy
  have hpos : 0 < D - 4 * q * y := by linarith
  have e : 2 * q / (D - 4 * q * y) * x * y - 2 * q * x * y / D =
      8 * q ^ 2 * x * y ^ 2 / (D * (D - 4 * q * y)) := by
    have hne : D - 4 * q * y ≠ 0 := hpos.ne'
    rw [eq_div_iff (mul_ne_zero hD.ne' hne)]
    have h1 : 2 * q / (D - 4 * q * y) * (D - 4 * q * y) = 2 * q := div_mul_cancel₀ _ hne
    have h2 : 2 * q * x * y / D * D = 2 * q * x * y := div_mul_cancel₀ _ hD.ne'
    linear_combination (x * y * D) * h1 - (D - 4 * q * y) * h2
  rw [e, abs_div, abs_of_pos (mul_pos hD hpos), div_le_iff₀ (mul_pos hD hpos)]
  have hy2 : y ^ 2 ≤ 4 := by
    have := sq_abs y; nlinarith [abs_nonneg y]
  have h1 : |8 * q ^ 2 * x * y ^ 2| = 8 * q ^ 2 * |x| * y ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 8 * q ^ 2),
      abs_of_nonneg (sq_nonneg y)]
  rw [h1]
  have hK : 32 * |x| ≤ 64 * |x| / D ^ 2 * (D * (D - 4 * q * y)) := by
    rw [show 64 * |x| / D ^ 2 * (D * (D - 4 * q * y)) = 64 * |x| * ((D - 4 * q * y) / D) by
      field_simp]
    have : 1 / 2 ≤ (D - 4 * q * y) / D := by rw [le_div_iff₀ hD]; linarith
    nlinarith [abs_nonneg x]
  have hq2' : 0 ≤ q ^ 2 := sq_nonneg q
  calc 8 * q ^ 2 * |x| * y ^ 2 ≤ 8 * q ^ 2 * |x| * 4 := by
        apply mul_le_mul_of_nonneg_left hy2; positivity
    _ = q ^ 2 * (32 * |x|) := by ring
    _ ≤ q ^ 2 * (64 * |x| / D ^ 2 * (D * (D - 4 * q * y))) :=
        mul_le_mul_of_nonneg_left hK hq2'
    _ = 64 * |x| / D ^ 2 * q ^ 2 * (D * (D - 4 * q * y)) := by ring

theorem X7_cohb (q x S y D : ℝ) (hD : 0 < D) (hq : 0 ≤ q) (hq2 : 16 * q ≤ D) (hy : |y| ≤ 2)
    (hS : |S| ≤ 1) :
    |x * S * (4 * q * y / (D * (D - 4 * q * y)))| ≤ 16 * |x| / D ^ 2 * q := by
  have hden := X7_den q y D hD hq hq2 hy
  have hpos : 0 < D - 4 * q * y := by linarith
  rw [abs_mul, abs_mul, abs_div, abs_mul, abs_mul, abs_of_nonneg hq,
    abs_of_pos (mul_pos hD hpos), abs_of_pos (by norm_num : (0:ℝ) < 4)]
  have h1 : 4 * q * |y| / (D * (D - 4 * q * y)) ≤ 16 * q / D ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos hD hpos) (by positivity)]
    have : D * (D / 2) ≤ D * (D - 4 * q * y) := mul_le_mul_of_nonneg_left hden hD.le
    have a1 : 4 * q * |y| * D ^ 2 ≤ 8 * q * D ^ 2 := by
      have := mul_le_mul_of_nonneg_left hy (mul_nonneg hq (sq_nonneg D)); nlinarith
    have a2 : 8 * q * D ^ 2 ≤ 16 * q * (D * (D - 4 * q * y)) := by
      have := mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 16 * q); nlinarith
    linarith
  have h2 : 0 ≤ 4 * q * |y| / (D * (D - 4 * q * y)) := by positivity
  calc |x| * |S| * (4 * q * |y| / (D * (D - 4 * q * y)))
      ≤ |x| * 1 * (16 * q / D ^ 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hS (abs_nonneg x)) h1 h2
        positivity
    _ = 16 * |x| / D ^ 2 * q := by ring

theorem X7_cohid (c : ℂ) (x S s L D q y : ℝ) (hD : 0 < D) (hpos : 0 < D - 4 * q * y) :
    -c * (x : ℂ) * (S : ℂ) * ((s : ℂ) + Complex.I * (L : ℂ)) / ((D - 4 * q * y : ℝ) : ℂ) -
      (-c * (x : ℂ) * (S : ℂ) / (Real.sqrt D : ℂ) * (((s : ℂ) + Complex.I * (L : ℂ)) / (Real.sqrt D : ℂ))) =
    ((-(x * S * (4 * q * y / (D * (D - 4 * q * y)))) : ℝ) : ℂ) * (c * ((s : ℂ) + Complex.I * (L : ℂ))) := by
  have hsD : (Real.sqrt D : ℂ) * (Real.sqrt D : ℂ) = (D : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hD.le]
  have hw : (Real.sqrt D : ℂ) ≠ 0 := by
    have := Real.sqrt_pos.mpr hD; exact_mod_cast this.ne'
  have hK : (D : ℂ) - 4 * q * y ≠ 0 := by exact_mod_cast hpos.ne'
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  rw [div_mul_div_comm, mul_div_assoc, show (Real.sqrt D : ℂ) * (Real.sqrt D : ℂ) = D from hsD]
  field_simp
  ring

theorem X7_norm_sL (s L : ℝ) : ‖(s : ℂ) + Complex.I * (L : ℂ)‖ = Real.sqrt (L ^ 2 + s ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring

theorem X7_y_bound (m : Model) : |angleC m * differenceL m| ≤ 2 := by
  have h1 : |angleC m| ≤ 1 := Real.abs_cos_le_one _
  have h2 : |differenceL m| ≤ 2 := by
    unfold differenceL
    have := Real.abs_cos_le_one (m.frequency * m.duration)
    calc _ ≤ |angleC m| + |Real.cos (m.frequency * m.duration)| := abs_sub _ _
      _ ≤ 2 := by linarith
  rw [abs_mul]
  nlinarith [abs_nonneg (angleC m), abs_nonneg (differenceL m)]

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution (m : Model) (hp : 0 < m.pA) (hp1 : m.pA < 1)
    (hD : 0 < denominatorD m) :
    (∃ delta : ℝ, 0 < delta ∧ ∀ c : ℂ, ‖c‖ < delta →
      Physical m.pA c ∧ 0 < denominatorD m - 4 * Complex.normSq c * angleC m * differenceL m) ∧
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun c => varyingPopulation m c - (m.pA +
        2 * Complex.normSq c * (2 * m.pA - 1) * angleC m * differenceL m / denominatorD m))
      (fun c : ℂ => ‖c‖ ^ 4) ∧
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun c => varyingCoherence m c -
        (-c * (2 * m.pA - 1 : ℝ) * (angleS m : ℂ) /
          (Real.sqrt (denominatorD m) : ℂ) * phase m))
      (fun c : ℂ => ‖c‖ ^ 3) := by
  set D := denominatorD m with hDdef
  set y := angleC m * differenceL m with hydef
  have hy : |y| ≤ 2 := X7_y_bound m
  have hpp : 0 < m.pA * (1 - m.pA) := mul_pos hp (by linarith)
  set e := min (m.pA * (1 - m.pA)) (D / 16) with he
  have hep : 0 < e := lt_min hpp (by linarith)
  have hsmall : ∀ c : ℂ, ‖c‖ < Real.sqrt e →
      Complex.normSq c ≤ m.pA * (1 - m.pA) ∧ 16 * Complex.normSq c ≤ D := by
    intro c hc
    have h0 : Complex.normSq c < e := by
      rw [Complex.normSq_eq_norm_sq]
      have := Real.lt_sqrt (norm_nonneg c) |>.mp hc
      exact this
    exact ⟨by linarith [min_le_left (m.pA * (1 - m.pA)) (D / 16)],
      by linarith [min_le_right (m.pA * (1 - m.pA)) (D / 16)]⟩
  have hev : ∀ᶠ c : ℂ in 𝓝 0, ‖c‖ < Real.sqrt e := by
    have : Metric.ball (0 : ℂ) (Real.sqrt e) ∈ 𝓝 (0 : ℂ) :=
      Metric.ball_mem_nhds 0 (Real.sqrt_pos.mpr hep)
    filter_upwards [this] with c hc
    simpa using hc
  refine ⟨⟨Real.sqrt e, Real.sqrt_pos.mpr hep, fun c hc => ?_⟩, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hsmall c hc
    refine ⟨⟨hp.le, hp1.le, h1⟩, ?_⟩
    have := X7_den (Complex.normSq c) y D hD (Complex.normSq_nonneg c) h2 hy
    have : 4 * Complex.normSq c * angleC m * differenceL m = 4 * Complex.normSq c * y := by
      rw [hydef]; ring
    linarith
  · apply Asymptotics.IsBigO.of_bound (64 * |2 * m.pA - 1| / D ^ 2)
    filter_upwards [hev] with c hc
    obtain ⟨_, h2⟩ := hsmall c hc
    have hb := X7_popb (Complex.normSq c) (2 * m.pA - 1) y D hD (Complex.normSq_nonneg c) h2 hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm,
      show ‖c‖ ^ 4 = (Complex.normSq c) ^ 2 by rw [Complex.normSq_eq_norm_sq]; ring]
    have e1 : varyingPopulation m c - (m.pA +
        2 * Complex.normSq c * (2 * m.pA - 1) * angleC m * differenceL m / D) =
        2 * Complex.normSq c / (D - 4 * Complex.normSq c * y) * (2 * m.pA - 1) * y -
          2 * Complex.normSq c * (2 * m.pA - 1) * y / D := by
      unfold varyingPopulation; rw [← hDdef, hydef]; ring
    rw [e1]
    convert hb using 2 <;> ring
  · apply Asymptotics.IsBigO.of_bound (16 * |2 * m.pA - 1| / D ^ 2 * Real.sqrt D)
    filter_upwards [hev] with c hc
    obtain ⟨_, h2⟩ := hsmall c hc
    have hq : 0 ≤ Complex.normSq c := Complex.normSq_nonneg c
    have hden := X7_den (Complex.normSq c) y D hD hq h2 hy
    have hpos : 0 < D - 4 * Complex.normSq c * y := by linarith
    have hyy : (denominatorD m - 4 * Complex.normSq c * angleC m * differenceL m : ℝ) =
        D - 4 * Complex.normSq c * y := by rw [hydef, hDdef]; ring
    have e1 := X7_cohid c (2 * m.pA - 1) (angleS m) (Real.sin (m.frequency * m.duration))
      (differenceL m) D (Complex.normSq c) y hD hpos
    have hv : varyingCoherence m c - (-c * ((2 * m.pA - 1 : ℝ) : ℂ) * (angleS m : ℂ) /
        (Real.sqrt (denominatorD m) : ℂ) * phase m) =
        (((-((2 * m.pA - 1) * angleS m * (4 * Complex.normSq c * y /
          (D * (D - 4 * Complex.normSq c * y))))) : ℝ) : ℂ) *
          (c * ((Real.sin (m.frequency * m.duration) : ℂ) + Complex.I * (differenceL m : ℂ))) := by
      refine Eq.trans ?_ e1
      unfold varyingCoherence phase
      rw [hyy, ← hDdef]
    rw [hv, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, Real.norm_eq_abs,
      abs_pow, abs_norm, X7_norm_sL]
    have hDe : differenceL m ^ 2 + Real.sin (m.frequency * m.duration) ^ 2 = D := by
      rw [hDdef]; rfl
    rw [hDe]
    have hb := X7_cohb (Complex.normSq c) (2 * m.pA - 1) (angleS m) y D hD hq h2 hy
      (Real.abs_sin_le_one _)
    have hq' : Complex.normSq c = ‖c‖ ^ 2 := Complex.normSq_eq_norm_sq c
    have hsDn : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
    calc |(2 * m.pA - 1) * angleS m * (4 * Complex.normSq c * y / (D * (D - 4 * Complex.normSq c * y)))| * (‖c‖ * Real.sqrt D)
        ≤ (16 * |2 * m.pA - 1| / D ^ 2 * Complex.normSq c) * (‖c‖ * Real.sqrt D) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 16 * |2 * m.pA - 1| / D ^ 2 * Real.sqrt D * ‖c‖ ^ 3 := by rw [hq']; ring
