-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P44.offdiagonal_stationarity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:52:56.290896+00:00
-- url     : https://prove2.me/submissions/4c98d26f-c847-40ee-8381-507481eeb5e1

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44
noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

theorem g68l_quad_pos (a b c1 c2 : ℝ) (h : PhysicalResource (standardCov a b c1 c2))
    (w : PairMode → ℝ) (q : ℝ) (k : PairMode)
    (hq : star (fun i => (w i : ℂ)) ⬝ᵥ ((QAlgorithms.Papers.Independent.Dependency50.P10.complexify
      (standardCov a b c1 c2) - Complex.I • QAlgorithms.Papers.Independent.Dependency50.P10.complexify
        (Matrix.fromBlocks modeSymplecticForm 0 0 modeSymplecticForm)) *ᵥ (fun i => (w i : ℂ))) = (q : ℂ))
    (hk : ((QAlgorithms.Papers.Independent.Dependency50.P10.complexify
      (standardCov a b c1 c2) - Complex.I • QAlgorithms.Papers.Independent.Dependency50.P10.complexify
        (Matrix.fromBlocks modeSymplecticForm 0 0 modeSymplecticForm)) *ᵥ (fun i => (w i : ℂ))) k ≠ 0) :
    0 < q := by
  obtain ⟨_, hP⟩ := h
  have h0 := hP.dotProduct_mulVec_nonneg (fun i => (w i : ℂ))
  rw [hq] at h0
  have ge : 0 ≤ q := Complex.zero_le_real.mp h0
  rcases ge.lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := (hP.dotProduct_mulVec_zero_iff _).mp (by rw [hq, ← h]; simp)
    exact hk (congrFun hz k)

theorem g68l_alpha_pos (a b c1 c2 x : ℝ) (h : PhysicalResource (standardCov a b c1 c2)) :
    0 < a + 2 * c1 * x + b * x ^ 2 := by
  apply g68l_quad_pos a b c1 c2 h (Sum.elim ![1, 0] ![x, 0]) _ (Sum.inl 1)
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
      QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]
    ring
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
      QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]

theorem g68l_beta_pos (a b c1 c2 y : ℝ) (h : PhysicalResource (standardCov a b c1 c2)) :
    0 < a - 2 * c2 * y + b * y ^ 2 := by
  apply g68l_quad_pos a b c1 c2 h (Sum.elim ![0, 1] ![0, -y]) _ (Sum.inl 0)
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
      QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]
    ring
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
      QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]

theorem g68l_d_nonneg (d1 d2 : ℝ) (hD : InputOrProcess (!![d1, 0; 0, d2] : QuadratureMatrix)) :
    0 ≤ d1 ∧ 0 ≤ d2 := by
  rcases hD with ⟨⟨_, hP⟩, _⟩ | h
  · have h1 := hP.dotProduct_mulVec_nonneg (Pi.single 0 1)
    have h2 := hP.dotProduct_mulVec_nonneg (Pi.single 1 1)
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm, Pi.single_apply] at h1 h2
    exact ⟨h1, h2⟩
  · have h1 := congrFun (congrFun h 0) 0
    have h2 := congrFun (congrFun h 1) 1
    simp at h1 h2
    exact ⟨h1.ge, h2.ge⟩

theorem g68l_formula1 (a b c1 c2 d1 d2 x y t : ℝ) :
    reducedDet !![d1, 0; 0, d2] (a • (1 : QuadratureMatrix)) (b • (1 : QuadratureMatrix)) !![c1, 0; 0, c2]
      !![x, t; 0, y] = (|1 - x * y| + Real.sqrt ((2 * d1 + a + 2 * c1 * x + b * x ^ 2) *
        (2 * d2 + a - 2 * c2 * y + b * y ^ 2) + (b * (2 * d2 + a - 2 * c2 * y + b * y ^ 2) - (b * y - c2) ^ 2) * t ^ 2)) ^ 2 := by
  have hM : noiseBase !![d1, 0; 0, d2] (a • (1 : QuadratureMatrix)) (b • (1 : QuadratureMatrix))
      !![c1, 0; 0, c2] !![x, t; 0, y] = !![2 * d1 + a + 2 * c1 * x + b * x ^ 2 + b * t ^ 2, t * (b * y - c2);
        t * (b * y - c2), 2 * d2 + a - 2 * c2 * y + b * y ^ 2] := by
    ext i j
    simp only [noiseBase, reflect, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [reducedDet, hM, Matrix.det_fin_two_of, Matrix.det_fin_two_of]
  congr 3 <;> ring

theorem g68l_formula2 (a b c1 c2 d1 d2 x y t : ℝ) :
    reducedDet !![d1, 0; 0, d2] (a • (1 : QuadratureMatrix)) (b • (1 : QuadratureMatrix)) !![c1, 0; 0, c2]
      !![x, 0; t, y] = (|1 - x * y| + Real.sqrt ((2 * d1 + a + 2 * c1 * x + b * x ^ 2) *
        (2 * d2 + a - 2 * c2 * y + b * y ^ 2) + (b * (2 * d1 + a + 2 * c1 * x + b * x ^ 2) - (c1 + b * x) ^ 2) * t ^ 2)) ^ 2 := by
  have hM : noiseBase !![d1, 0; 0, d2] (a • (1 : QuadratureMatrix)) (b • (1 : QuadratureMatrix))
      !![c1, 0; 0, c2] !![x, 0; t, y] = !![2 * d1 + a + 2 * c1 * x + b * x ^ 2, t * (c1 + b * x);
        t * (c1 + b * x), 2 * d2 + a - 2 * c2 * y + b * y ^ 2 + b * t ^ 2] := by
    ext i j
    simp only [noiseBase, reflect, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [reducedDet, hM, Matrix.det_fin_two_of, Matrix.det_fin_two_of]
  congr 3 <;> ring

theorem g68l_even_deriv (K P0 g : ℝ) (hP : 0 < P0) :
    HasDerivAt (fun t : ℝ => (K + Real.sqrt (P0 + g * t ^ 2)) ^ 2) 0 0 := by
  have h1 : HasDerivAt (fun t : ℝ => P0 + g * t ^ 2) 0 0 := by
    have := ((hasDerivAt_pow 2 (0 : ℝ)).const_mul g).const_add P0
    simpa using this
  have h2 := h1.sqrt (by simp; exact hP.ne')
  have h3 := (h2.const_add K).fun_pow 2
  simpa using h3

/-- PDF p.5, Eq.(42): two coordinate derivatives of (40) vanish at diagonal
S, including det S=1. No joint differentiability or diagonal optimality claimed. -/
theorem solution (a b c1 c2 d1 d2 x y : ℝ)
    (hresource : PhysicalResource (standardCov a b c1 c2))
    (hD : InputOrProcess (!![d1, 0; 0, d2] : QuadratureMatrix)) :
    HasDerivAt (fun t : ℝ => reducedDet !![d1, 0; 0, d2]
      (a • (1 : QuadratureMatrix)) (b • (1 : QuadratureMatrix)) !![c1, 0; 0, c2] !![x, t; 0, y]) 0 0 ∧
    HasDerivAt (fun t : ℝ => reducedDet !![d1, 0; 0, d2]
      (a • (1 : QuadratureMatrix)) (b • (1 : QuadratureMatrix)) !![c1, 0; 0, c2] !![x, 0; t, y]) 0 0 := by
  have ha := g68l_alpha_pos a b c1 c2 x hresource
  have hb := g68l_beta_pos a b c1 c2 y hresource
  obtain ⟨hd1, hd2⟩ := g68l_d_nonneg d1 d2 hD
  have hP : 0 < (2 * d1 + a + 2 * c1 * x + b * x ^ 2) * (2 * d2 + a - 2 * c2 * y + b * y ^ 2) :=
    mul_pos (by linarith) (by linarith)
  constructor
  · simp only [g68l_formula1]
    exact g68l_even_deriv _ _ _ hP
  · simp only [g68l_formula2]
    exact g68l_even_deriv _ _ _ hP



end
