-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.principalSymbol_polarizationIndependent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:38:19.55378+00:00
-- url     : https://prove2.me/submissions/4bfdee2c-110f-49e9-8656-47568ec45231

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

theorem g64h_LeL (g c a0 a1 a2 s : ℝ) (hs : s = a0 ^ 2 + a1 ^ 2 + a2 ^ 2) (hs0 : s ≠ 0) (hc0 : c ≠ 0)
    (hγ : g ^ 2 * (c ^ 2 - s) - c ^ 2 = 0) :
    !![g, g * a0 / c, g * a1 / c, g * a2 / c; g * a0 / c, 1 + (g - 1) * a0 * a0 / s, (g - 1) * a0 * a1 / s, (g - 1) * a0 * a2 / s; g * a1 / c, (g - 1) * a1 * a0 / s, 1 + (g - 1) * a1 * a1 / s, (g - 1) * a1 * a2 / s; g * a2 / c, (g - 1) * a2 * a0 / s, (g - 1) * a2 * a1 / s, 1 + (g - 1) * a2 * a2 / s] * !![(1:ℝ), 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] * (!![g, g * a0 / c, g * a1 / c, g * a2 / c; g * a0 / c, 1 + (g - 1) * a0 * a0 / s, (g - 1) * a0 * a1 / s, (g - 1) * a0 * a2 / s; g * a1 / c, (g - 1) * a1 * a0 / s, 1 + (g - 1) * a1 * a1 / s, (g - 1) * a1 * a2 / s; g * a2 / c, (g - 1) * a2 * a0 / s, (g - 1) * a2 * a1 / s, 1 + (g - 1) * a2 * a2 / s]).transpose = !![(1:ℝ), 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  subst hs
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · linear_combination (norm := skip) (1 / c ^ 2) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a0 * a0) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a0 * a1) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a0 * a2) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a1 * a0) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a1 * a1) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a1 * a2) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a2 * a0) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a2 * a1) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a2 * a2) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring

theorem g64h_LGL (g c n a0 a1 a2 s : ℝ) (hs : s = a0 ^ 2 + a1 ^ 2 + a2 ^ 2) (hs0 : s ≠ 0) (hc0 : c ≠ 0)
    (hγ : g ^ 2 * (c ^ 2 - s) - c ^ 2 = 0) :
    !![g, g * a0 / c, g * a1 / c, g * a2 / c; g * a0 / c, 1 + (g - 1) * a0 * a0 / s, (g - 1) * a0 * a1 / s, (g - 1) * a0 * a2 / s; g * a1 / c, (g - 1) * a1 * a0 / s, 1 + (g - 1) * a1 * a1 / s, (g - 1) * a1 * a2 / s; g * a2 / c, (g - 1) * a2 * a0 / s, (g - 1) * a2 * a1 / s, 1 + (g - 1) * a2 * a2 / s] * !![n ^ 2, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] * (!![g, g * a0 / c, g * a1 / c, g * a2 / c; g * a0 / c, 1 + (g - 1) * a0 * a0 / s, (g - 1) * a0 * a1 / s, (g - 1) * a0 * a2 / s; g * a1 / c, (g - 1) * a1 * a0 / s, 1 + (g - 1) * a1 * a1 / s, (g - 1) * a1 * a2 / s; g * a2 / c, (g - 1) * a2 * a0 / s, (g - 1) * a2 * a1 / s, 1 + (g - 1) * a2 * a2 / s]).transpose = !![1 + (n ^ 2 - 1) * (g) * (g), 0 + (n ^ 2 - 1) * (g) * (g * a0 / c), 0 + (n ^ 2 - 1) * (g) * (g * a1 / c), 0 + (n ^ 2 - 1) * (g) * (g * a2 / c); 0 + (n ^ 2 - 1) * (g * a0 / c) * (g), -1 + (n ^ 2 - 1) * (g * a0 / c) * (g * a0 / c), 0 + (n ^ 2 - 1) * (g * a0 / c) * (g * a1 / c), 0 + (n ^ 2 - 1) * (g * a0 / c) * (g * a2 / c); 0 + (n ^ 2 - 1) * (g * a1 / c) * (g), 0 + (n ^ 2 - 1) * (g * a1 / c) * (g * a0 / c), -1 + (n ^ 2 - 1) * (g * a1 / c) * (g * a1 / c), 0 + (n ^ 2 - 1) * (g * a1 / c) * (g * a2 / c); 0 + (n ^ 2 - 1) * (g * a2 / c) * (g), 0 + (n ^ 2 - 1) * (g * a2 / c) * (g * a0 / c), 0 + (n ^ 2 - 1) * (g * a2 / c) * (g * a1 / c), -1 + (n ^ 2 - 1) * (g * a2 / c) * (g * a2 / c)] := by
  subst hs
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  · linear_combination (norm := skip) (1 / c ^ 2) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a0 * a0) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a0 * a1) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a0 * a2) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a1 * a0) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a1 * a1) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a1 * a2) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (0) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a2 * a0) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a2 * a1) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring
  · linear_combination (norm := skip) (-(a2 * a2) / (c ^ 2 * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))) * hγ
    field_simp
    ring

theorem g64h_Lexp (c : ℝ) (u : V3) (hu0 : u ≠ 0) : lorentzBoost c u = !![(lorentzFactor c u), (lorentzFactor c u) * (u 0) / c, (lorentzFactor c u) * (u 1) / c, (lorentzFactor c u) * (u 2) / c; (lorentzFactor c u) * (u 0) / c, 1 + ((lorentzFactor c u) - 1) * (u 0) * (u 0) / (dot3 u u), ((lorentzFactor c u) - 1) * (u 0) * (u 1) / (dot3 u u), ((lorentzFactor c u) - 1) * (u 0) * (u 2) / (dot3 u u); (lorentzFactor c u) * (u 1) / c, ((lorentzFactor c u) - 1) * (u 1) * (u 0) / (dot3 u u), 1 + ((lorentzFactor c u) - 1) * (u 1) * (u 1) / (dot3 u u), ((lorentzFactor c u) - 1) * (u 1) * (u 2) / (dot3 u u); (lorentzFactor c u) * (u 2) / c, ((lorentzFactor c u) - 1) * (u 2) * (u 0) / (dot3 u u), ((lorentzFactor c u) - 1) * (u 2) * (u 1) / (dot3 u u), 1 + ((lorentzFactor c u) - 1) * (u 2) * (u 2) / (dot3 u u)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lorentzBoost, hu0]

theorem g64h_eta : minkowskiMetric = !![(1:ℝ), 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowskiMetric]

theorem g64h_g0 (c n : ℝ) : gUp c n 0 = !![n ^ 2, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gUp, fourFlow, lorentzFactor, minkowskiMetric, dot3]

theorem g64h_gu (c n : ℝ) (u : V3) : gUp c n u = !![1 + (n ^ 2 - 1) * ((lorentzFactor c u)) * ((lorentzFactor c u)), 0 + (n ^ 2 - 1) * ((lorentzFactor c u)) * ((lorentzFactor c u) * (u 0) / c), 0 + (n ^ 2 - 1) * ((lorentzFactor c u)) * ((lorentzFactor c u) * (u 1) / c), 0 + (n ^ 2 - 1) * ((lorentzFactor c u)) * ((lorentzFactor c u) * (u 2) / c); 0 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 0) / c) * ((lorentzFactor c u)), -1 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 0) / c) * ((lorentzFactor c u) * (u 0) / c), 0 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 0) / c) * ((lorentzFactor c u) * (u 1) / c), 0 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 0) / c) * ((lorentzFactor c u) * (u 2) / c); 0 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 1) / c) * ((lorentzFactor c u)), 0 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 1) / c) * ((lorentzFactor c u) * (u 0) / c), -1 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 1) / c) * ((lorentzFactor c u) * (u 1) / c), 0 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 1) / c) * ((lorentzFactor c u) * (u 2) / c); 0 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 2) / c) * ((lorentzFactor c u)), 0 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 2) / c) * ((lorentzFactor c u) * (u 0) / c), 0 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 2) / c) * ((lorentzFactor c u) * (u 1) / c), -1 + (n ^ 2 - 1) * ((lorentzFactor c u) * (u 2) / c) * ((lorentzFactor c u) * (u 2) / c)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gUp, fourFlow, minkowskiMetric]

theorem g64h_quad (G L : M4) (p : V4) :
    quadratic G (apply4 L.transpose p) = quadratic (L * G * L.transpose) p := by
  simp only [quadratic, apply4, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  simp only [Fin.sum_univ_four]
  ring

/-- PDF p.4, (19)–(32): Lorentz transformation of the frozen wave symbol.
The same scalar acts on every polarization component; amplitude transport is excluded. -/
theorem solution (c n : ℝ) (u : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) :
    lorentzBoost c u * minkowskiMetric * (lorentzBoost c u).transpose = minkowskiMetric ∧
    gUp c n u = lorentzBoost c u * gUp c n 0 * (lorentzBoost c u).transpose ∧
    (∀ p : V4,
      quadratic (gUp c n 0) (apply4 (lorentzBoost c u).transpose p) =
        quadratic (gUp c n u) p) ∧
    (∀ (p : V4) (F : Matrix (Fin 4) (Fin 4) ℂ),
      let L : Matrix (Fin 4) (Fin 4) ℂ := (lorentzBoost c u).map (fun a => (a : ℂ))
      ((quadratic (gUp c n 0) (apply4 (lorentzBoost c u).transpose p) : ℝ) : ℂ) •
          (L.transpose * F * L) =
        L.transpose * (((quadratic (gUp c n u) p : ℝ) : ℂ) • F) * L) := by
  have h1 : lorentzBoost c u * minkowskiMetric * (lorentzBoost c u).transpose = minkowskiMetric ∧
      gUp c n u = lorentzBoost c u * gUp c n 0 * (lorentzBoost c u).transpose := by
    by_cases hu0 : u = 0
    · subst hu0
      simp [lorentzBoost]
    have hs' : dot3 u u = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by simp [dot3, Fin.sum_univ_three]; ring
    have hspos : dot3 u u ≠ 0 := by
      intro h0
      apply hu0
      have h0' : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 0 := by rw [← hs', h0]
      ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
    have hc2 : 0 < c ^ 2 := by positivity
    have hpos : 0 < 1 - dot3 u u / c ^ 2 := by rw [sub_pos, div_lt_one hc2]; exact hu
    have hcs : c ^ 2 - dot3 u u ≠ 0 := by linarith
    have hγ : lorentzFactor c u ^ 2 * (c ^ 2 - dot3 u u) - c ^ 2 = 0 := by
      rw [lorentzFactor, div_pow, Real.sq_sqrt hpos.le]; field_simp; ring
    rw [g64h_Lexp c u hu0, g64h_eta, g64h_g0, g64h_gu]
    exact ⟨g64h_LeL _ _ _ _ _ _ hs' hspos hc.ne' hγ, (g64h_LGL _ _ _ _ _ _ _ hs' hspos hc.ne' hγ).symm⟩
  have h3 : ∀ p : V4, quadratic (gUp c n 0) (apply4 (lorentzBoost c u).transpose p) =
      quadratic (gUp c n u) p := by
    intro p; rw [g64h_quad, ← h1.2]
  refine ⟨h1.1, h1.2, h3, fun p F => ?_⟩
  simp only
  rw [h3 p, Matrix.mul_smul, Matrix.smul_mul]


end

