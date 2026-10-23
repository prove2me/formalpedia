-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P44.diagonal_candidates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T09:46:03.214575+00:00
-- url     : https://prove2.me/submissions/158b1cf4-6c10-4cb9-af1c-4cadd75d863c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

open scoped Matrix ComplexOrder

namespace X7Diag
open QAlgorithms.Papers.Independent.Claimed50.P44
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

lemma X7_form1 (a b c1 c2 : ℝ) (h : PhysicalResource (standardCov a b c1 c2)) (x t : ℝ) :
    0 ≤ a + 2 * c1 * x + b * x ^ 2 + a * t ^ 2 + 2 * t := by
  have hM := h.2.dotProduct_mulVec_nonneg
    (Sum.elim ![(1 : ℂ), Complex.I * t] ![(x : ℂ), 0])
  rw [Complex.nonneg_iff] at hM
  have h1 := hM.1
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks,
    complexify, standardCov, resourceCov, modeSymplecticForm] at h1
  nlinarith [h1]

open QAlgorithms.Papers.Independent.Claimed50.P44
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

lemma X7_form2 (a b c1 c2 : ℝ) (h : PhysicalResource (standardCov a b c1 c2)) (y t : ℝ) :
    0 ≤ a - 2 * c2 * y + b * y ^ 2 + a * t ^ 2 - 2 * t := by
  have hM := h.2.dotProduct_mulVec_nonneg
    (Sum.elim ![Complex.I * t, (1 : ℂ)] ![0, -(y : ℂ)])
  rw [Complex.nonneg_iff] at hM
  have h1 := hM.1
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks,
    complexify, standardCov, resourceCov, modeSymplecticForm] at h1
  nlinarith [h1]

lemma X7_dnonneg (d1 d2 : ℝ) (hD : InputOrProcess (!![d1, 0; 0, d2] : QuadratureMatrix)) :
    0 ≤ d1 ∧ 0 ≤ d2 := by
  rcases hD with hD | hD
  · have hM := hD.1.2.dotProduct_mulVec_nonneg ![(1 : ℂ), 0]
    have hM2 := hD.1.2.dotProduct_mulVec_nonneg ![(0 : ℂ), 1]
    rw [Complex.nonneg_iff] at hM hM2
    have h1 := hM.1
    have h2 := hM2.1
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, complexify, modeSymplecticForm] at h1 h2
    exact ⟨h1, h2⟩
  · have e1 := congrFun (congrFun hD 0) 0
    have e2 := congrFun (congrFun hD 1) 1
    simp at e1 e2
    exact ⟨e1.ge, e2.ge⟩


lemma X7_Fpos (a b c1 c2 d1 : ℝ) (h : PhysicalResource (standardCov a b c1 c2)) (hd : 0 ≤ d1)
    (x : ℝ) : 0 < firstBaseVariance a b c1 d1 x := by
  have ha : 0 ≤ a := by have := X7_form1 a b c1 c2 h 0 0; simpa using this
  set s : ℝ := 1 / (a + 1) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have has : a * s < 1 := by
    rw [hs, mul_one_div, div_lt_one (by linarith)]; linarith
  have h1 := X7_form1 a b c1 c2 h x (-s)
  unfold firstBaseVariance
  nlinarith [mul_pos hs0 (by linarith : (0:ℝ) < 2 - a * s)]

lemma X7_Spos (a b c1 c2 d2 : ℝ) (h : PhysicalResource (standardCov a b c1 c2)) (hd : 0 ≤ d2)
    (y : ℝ) : 0 < secondBaseVariance a b c2 d2 y := by
  have ha : 0 ≤ a := by have := X7_form2 a b c1 c2 h 0 0; simpa using this
  set s : ℝ := 1 / (a + 1) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have has : a * s < 1 := by
    rw [hs, mul_one_div, div_lt_one (by linarith)]; linarith
  have h1 := X7_form2 a b c1 c2 h y s
  unfold secondBaseVariance
  nlinarith [mul_pos hs0 (by linarith : (0:ℝ) < 2 - a * s)]
end X7Diag

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

open QAlgorithms.Papers.Independent.Claimed50.P44 X7Diag in
theorem solution (a b c1 c2 d1 d2 : ℝ)
    (hresource : PhysicalResource (standardCov a b c1 c2))
    (hD : InputOrProcess (!![d1, 0; 0, d2] : QuadratureMatrix)) :
    (∀ x : ℝ, 0 < firstBaseVariance a b c1 d1 x) ∧
    (∀ y : ℝ, 0 < secondBaseVariance a b c2 d2 y) ∧
    (∀ x y : ℝ, x * y ≠ 1 →
      (DiagonalStationary a b c1 c2 d1 d2 x y ↔
        let sign : ℝ := if 1 - x * y > 0 then 1 else -1
        x = sign * Real.sqrt (firstBaseVariance a b c1 d1 x / secondBaseVariance a b c2 d2 y) * (b * y - c2) ∧
        y = sign * Real.sqrt (secondBaseVariance a b c2 d2 y / firstBaseVariance a b c1 d1 x) * (b * x + c1))) ∧
    (∀ x y : ℝ, x * y ≠ 1 → DiagonalStationary a b c1 c2 d1 d2 x y →
      let L := x * (b ^ 2 - 1) + b * c1
      L ≠ 0 → y = c2 * (b * x + c1) / L ∧
        c2 ^ 2 * firstBaseVariance a b c1 d1 x = L ^ 2 *
          secondBaseVariance a b c2 d2 (c2 * (b * x + c1) / L)) ∧
    (∀ x : ℝ, x ≠ 0 →
      HasDerivAt (fun z : ℝ => firstBaseVariance a b c1 d1 z * secondBaseVariance a b c2 d2 (1 / z))
        (2 * boundaryPolynomial a b c1 c2 d1 d2 x / x ^ 3) x ∧
      (HasDerivAt (fun z : ℝ => firstBaseVariance a b c1 d1 z * secondBaseVariance a b c2 d2 (1 / z)) 0 x ↔
        boundaryPolynomial a b c1 c2 d1 d2 x = 0)) := by
  obtain ⟨hd1, hd2⟩ := X7_dnonneg d1 d2 hD
  have hF : ∀ x, 0 < firstBaseVariance a b c1 d1 x := fun x => X7_Fpos a b c1 c2 d1 hresource hd1 x
  have hS : ∀ y, 0 < secondBaseVariance a b c2 d2 y := fun y => X7_Spos a b c1 c2 d2 hresource hd2 y
  have dF : ∀ x, HasDerivAt (fun z => firstBaseVariance a b c1 d1 z) (2 * c1 + 2 * b * x) x := by
    intro x
    unfold firstBaseVariance
    have := (((hasDerivAt_id x).const_mul (2 * c1)).const_add (2 * d1 + a)).add
      ((hasDerivAt_pow 2 x).const_mul b)
    refine this.congr_deriv ?_
    simp; ring
  have dS : ∀ y, HasDerivAt (fun z => secondBaseVariance a b c2 d2 z) (-2 * c2 + 2 * b * y) y := by
    intro y
    unfold secondBaseVariance
    have := (((hasDerivAt_id y).const_mul (2 * c2)).const_sub (2 * d2 + a)).add
      ((hasDerivAt_pow 2 y).const_mul b)
    refine this.congr_deriv ?_
    simp; ring
  -- part (3) as a reusable statement
  have part3 : ∀ x y : ℝ, x * y ≠ 1 →
      (DiagonalStationary a b c1 c2 d1 d2 x y ↔
        x = (if 1 - x * y > 0 then (1:ℝ) else -1) *
            Real.sqrt (firstBaseVariance a b c1 d1 x / secondBaseVariance a b c2 d2 y) *
            (b * y - c2) ∧
        y = (if 1 - x * y > 0 then (1:ℝ) else -1) *
            Real.sqrt (secondBaseVariance a b c2 d2 y / firstBaseVariance a b c1 d1 x) *
            (b * x + c1)) := by
    intro x y hxy
    set σ : ℝ := if 1 - x * y > 0 then (1:ℝ) else -1 with hσdef
    set F := firstBaseVariance a b c1 d1 x with hFdef
    set S := secondBaseVariance a b c2 d2 y with hSdef
    have hFx := hF x
    have hSy := hS y
    have hσ : σ = 1 ∨ σ = -1 := by
      rw [hσdef]; split_ifs <;> simp
    have dAx : HasDerivAt (fun z => |1 - z * y|) (σ * (-y)) x := by
      have hin : HasDerivAt (fun z => 1 - z * y) (-y) x := by
        have := ((hasDerivAt_id x).mul_const y).const_sub 1
        refine this.congr_deriv ?_; simp
      rw [hσdef]
      split_ifs with h
      · have := (hasDerivAt_abs_pos h).comp x hin
        refine this.congr_deriv ?_; ring
      · have hneg : 1 - x * y < 0 := by
          rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
          · exact h'
          · exact absurd (by linarith) hxy
        have := (hasDerivAt_abs_neg hneg).comp x hin
        refine this.congr_deriv ?_; ring
    have dAy : HasDerivAt (fun z => |1 - x * z|) (σ * (-x)) y := by
      have hin : HasDerivAt (fun z => 1 - x * z) (-x) y := by
        have := ((hasDerivAt_id y).const_mul x).const_sub 1
        refine this.congr_deriv ?_; simp
      rw [hσdef]
      split_ifs with h
      · have := (hasDerivAt_abs_pos h).comp y hin
        refine this.congr_deriv ?_; ring
      · have hneg : 1 - x * y < 0 := by
          rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
          · exact h'
          · exact absurd (by linarith) hxy
        have := (hasDerivAt_abs_neg hneg).comp y hin
        refine this.congr_deriv ?_; ring
    have hFS : F * S ≠ 0 := (mul_pos hFx hSy).ne'
    have dQx : HasDerivAt (fun z => Real.sqrt (firstBaseVariance a b c1 d1 z * S))
        ((2 * c1 + 2 * b * x) * S / (2 * Real.sqrt (F * S))) x :=
      ((dF x).mul_const S).sqrt hFS
    have dQy : HasDerivAt (fun z => Real.sqrt (F * secondBaseVariance a b c2 d2 z))
        (F * (-2 * c2 + 2 * b * y) / (2 * Real.sqrt (F * S))) y :=
      ((dS y).const_mul F).sqrt hFS
    have DX : HasDerivAt (fun z => diagonalObjective a b c1 c2 d1 d2 z y)
        (σ * (-y) + (2 * c1 + 2 * b * x) * S / (2 * Real.sqrt (F * S))) x := dAx.add dQx
    have DY : HasDerivAt (fun z => diagonalObjective a b c1 c2 d1 d2 x z)
        (σ * (-x) + F * (-2 * c2 + 2 * b * y) / (2 * Real.sqrt (F * S))) y := dAy.add dQy
    have hst : DiagonalStationary a b c1 c2 d1 d2 x y ↔
        (σ * (-y) + (2 * c1 + 2 * b * x) * S / (2 * Real.sqrt (F * S)) = 0 ∧
         σ * (-x) + F * (-2 * c2 + 2 * b * y) / (2 * Real.sqrt (F * S)) = 0) := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨DX.unique h1, DY.unique h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1 ▸ DX, h2 ▸ DY⟩
    rw [hst]
    have sF := Real.sqrt_pos.mpr hFx
    have sS := Real.sqrt_pos.mpr hSy
    have eFS : Real.sqrt (F * S) = Real.sqrt F * Real.sqrt S := Real.sqrt_mul hFx.le S
    have e1 : Real.sqrt (F / S) = Real.sqrt F / Real.sqrt S := Real.sqrt_div hFx.le S
    have e2 : Real.sqrt (S / F) = Real.sqrt S / Real.sqrt F := Real.sqrt_div hSy.le F
    have qF : Real.sqrt F * Real.sqrt F = F := Real.mul_self_sqrt hFx.le
    have qS : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hSy.le
    set u := Real.sqrt F
    set v := Real.sqrt S
    clear_value u v
    rw [eFS, e1, e2]
    rw [← qF, ← qS]
    have hu : u ≠ 0 := sF.ne'
    have hv : v ≠ 0 := sS.ne'
    rcases hσ with h | h <;> rw [h] <;> field_simp <;>
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  refine ⟨hF, hS, ?_, ?_, ?_⟩
  · intro x y hxy
    exact part3 x y hxy
  · intro x y hxy hst L hL
    obtain ⟨hx, hy⟩ := (part3 x y hxy).mp hst
    set σ : ℝ := if 1 - x * y > 0 then (1:ℝ) else -1 with hσdef
    have hσ2 : σ * σ = 1 := by rw [hσdef]; split_ifs <;> norm_num
    set F := firstBaseVariance a b c1 d1 x with hFdef
    set S := secondBaseVariance a b c2 d2 y with hSdef
    have hFx := hF x
    have hSy := hS y
    have sF := Real.sqrt_pos.mpr hFx
    have sS := Real.sqrt_pos.mpr hSy
    have e1 : Real.sqrt (F / S) = Real.sqrt F / Real.sqrt S := Real.sqrt_div hFx.le S
    have e2 : Real.sqrt (S / F) = Real.sqrt S / Real.sqrt F := Real.sqrt_div hSy.le F
    have qF : Real.sqrt F * Real.sqrt F = F := Real.mul_self_sqrt hFx.le
    have qS : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hSy.le
    rw [e1] at hx
    rw [e2] at hy
    have hu : Real.sqrt F ≠ 0 := sF.ne'
    have hv : Real.sqrt S ≠ 0 := sS.ne'
    have hxy' : x * y = (b * y - c2) * (b * x + c1) := by
      have hm := congrArg₂ (· * ·) hx hy
      rw [hm]
      have huv : (Real.sqrt F / Real.sqrt S) * (Real.sqrt S / Real.sqrt F) = 1 := by
        field_simp
      calc σ * (Real.sqrt F / Real.sqrt S) * (b * y - c2) * (σ * (Real.sqrt S / Real.sqrt F) * (b * x + c1))
          = (σ * σ) * ((Real.sqrt F / Real.sqrt S) * (Real.sqrt S / Real.sqrt F)) *
            ((b * y - c2) * (b * x + c1)) := by ring
        _ = (b * y - c2) * (b * x + c1) := by rw [hσ2, huv]; ring
    have hyL : y * L = c2 * (b * x + c1) := by
      simp only [L]; linear_combination (-1 : ℝ) * hxy'
    have hyv : y = c2 * (b * x + c1) / L := by
      rw [eq_div_iff hL]; exact hyL
    refine ⟨hyv, ?_⟩
    rw [← hyv]
    have hy2 : y ^ 2 * F = S * (b * x + c1) ^ 2 := by
      have : y * Real.sqrt F = σ * Real.sqrt S * (b * x + c1) := by
        rw [hy]; field_simp
      have h2 : (y * Real.sqrt F) ^ 2 = (σ * Real.sqrt S * (b * x + c1)) ^ 2 := by rw [this]
      have : (y * Real.sqrt F) ^ 2 = y ^ 2 * F := by rw [mul_pow, sq (Real.sqrt F), qF]
      have h3 : (σ * Real.sqrt S * (b * x + c1)) ^ 2 = S * (b * x + c1) ^ 2 := by
        rw [mul_pow, mul_pow, sq (Real.sqrt S), qS, sq σ, hσ2]; ring
      linarith
    have hx2 : x ^ 2 * S = F * (b * y - c2) ^ 2 := by
      have : x * Real.sqrt S = σ * Real.sqrt F * (b * y - c2) := by
        rw [hx]; field_simp
      have h2 : (x * Real.sqrt S) ^ 2 = (σ * Real.sqrt F * (b * y - c2)) ^ 2 := by rw [this]
      have : (x * Real.sqrt S) ^ 2 = x ^ 2 * S := by rw [mul_pow, sq (Real.sqrt S), qS]
      have h3 : (σ * Real.sqrt F * (b * y - c2)) ^ 2 = F * (b * y - c2) ^ 2 := by
        rw [mul_pow, mul_pow, sq (Real.sqrt F), qF, sq σ, hσ2]; ring
      linarith
    by_cases hk : b * x + c1 = 0
    · have hy0 : y = 0 := by
        rw [hk, mul_zero] at hyL
        rcases mul_eq_zero.mp hyL with h | h
        · exact h
        · exact absurd h hL
      have hLx : L = -x := by
        simp only [L]; have : c1 = -(b * x) := by linarith
        rw [this]; ring
      rw [hLx]
      rw [hy0] at hx2
      show c2 ^ 2 * F = (-x) ^ 2 * S
      nlinarith [hx2]
    · have hk2 : (b * x + c1) ^ 2 ≠ 0 := pow_ne_zero 2 hk
      apply mul_right_cancel₀ hk2
      have : c2 ^ 2 * F * (b * x + c1) ^ 2 = (y * L) ^ 2 * F := by rw [hyL]; ring
      rw [this]
      calc (y * L) ^ 2 * F = L ^ 2 * (y ^ 2 * F) := by ring
        _ = L ^ 2 * S * (b * x + c1) ^ 2 := by rw [hy2]; ring
  · intro x hx
    have hinv : HasDerivAt (fun z : ℝ => 1 / z) (-(x ^ 2)⁻¹) x := by
      simpa [one_div] using hasDerivAt_inv hx
    have dS' : HasDerivAt (fun z => secondBaseVariance a b c2 d2 (1 / z))
        ((-2 * c2 + 2 * b * (1 / x)) * (-(x ^ 2)⁻¹)) x :=
      (dS (1 / x)).comp x hinv
    have D := (dF x).mul dS'
    have D' : HasDerivAt (fun z : ℝ => firstBaseVariance a b c1 d1 z *
        secondBaseVariance a b c2 d2 (1 / z))
        (2 * boundaryPolynomial a b c1 c2 d1 d2 x / x ^ 3) x := by
      refine D.congr_deriv ?_
      unfold firstBaseVariance secondBaseVariance boundaryPolynomial
      field_simp
      ring
    refine ⟨D', ⟨fun h => ?_, fun h => ?_⟩⟩
    · have := D'.unique h
      have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx
      field_simp at this
      linarith
    · rw [h] at D'; simpa using D'
