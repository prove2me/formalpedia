-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P44.two_sided_noise_optimum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:48:11.712356+00:00
-- url     : https://prove2.me/submissions/cc617c05-8f8b-4fb2-b4f9-c8627a33db3d

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44
noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

theorem g68q_quad_pos (a b c1 c2 : ℝ) (h : PhysicalResource (standardCov a b c1 c2))
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

theorem g68q_alpha_pos (a b c1 c2 x : ℝ) (h : PhysicalResource (standardCov a b c1 c2)) :
    0 < a + 2 * c1 * x + b * x ^ 2 := by
  apply g68q_quad_pos a b c1 c2 h (Sum.elim ![1, 0] ![x, 0]) _ (Sum.inl 1)
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
      QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]
    ring
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
      QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]

theorem g68q_beta_pos (a b c1 c2 y : ℝ) (h : PhysicalResource (standardCov a b c1 c2)) :
    0 < a - 2 * c2 * y + b * y ^ 2 := by
  apply g68q_quad_pos a b c1 c2 h (Sum.elim ![0, 1] ![0, -y]) _ (Sum.inl 0)
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
      QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]
    ring
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
      QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]

theorem g68q_d_nonneg (d1 d2 : ℝ) (hD : InputOrProcess (!![d1, 0; 0, d2] : QuadratureMatrix)) :
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


theorem g68q_qa (a b c1 c2 u x : ℝ) (h : PhysicalResource (standardCov a b c1 c2)) (hux : u ≠ 0 ∨ x ≠ 0) :
    0 < a * u ^ 2 + 2 * c1 * u * x + b * x ^ 2 := by
  rcases hux with hu | hx
  · apply g68q_quad_pos a b c1 c2 h (Sum.elim ![u, 0] ![x, 0]) _ (Sum.inl 1)
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
        QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]
      ring
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
        QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm, hu]
  · apply g68q_quad_pos a b c1 c2 h (Sum.elim ![u, 0] ![x, 0]) _ (Sum.inr 1)
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
        QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]
      ring
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
        QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm, hx]

theorem g68q_qb (a b c1 c2 v y : ℝ) (h : PhysicalResource (standardCov a b c1 c2)) (hvy : v ≠ 0 ∨ y ≠ 0) :
    0 < a * v ^ 2 - 2 * c2 * v * y + b * y ^ 2 := by
  rcases hvy with hv | hy
  · apply g68q_quad_pos a b c1 c2 h (Sum.elim ![0, v] ![0, -y]) _ (Sum.inl 0)
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
        QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]
      ring
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
        QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm, hv]
  · apply g68q_quad_pos a b c1 c2 h (Sum.elim ![0, v] ![0, -y]) _ (Sum.inr 0)
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
        QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm]
      ring
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, standardCov, resourceCov,
        QAlgorithms.Papers.Independent.Dependency50.P10.complexify, modeSymplecticForm, hy]

theorem g68q_cs (al be g0 g1 g2 g3 : ℝ) (h1 : 0 ≤ al) (h2 : 0 ≤ be) (h3 : 0 ≤ g0) (h4 : 0 ≤ g1)
    (h5 : 0 ≤ g2) (h6 : 0 ≤ g3) :
    (Real.sqrt (al * be) + Real.sqrt (g0 * g1) + Real.sqrt (g2 * g3)) ^ 2 ≤ (al + g0 + g2) * (be + g1 + g3) := by
  rw [Real.sqrt_mul h1, Real.sqrt_mul h3, Real.sqrt_mul h5]
  have e1 := Real.sq_sqrt h1; have e2 := Real.sq_sqrt h2; have e3 := Real.sq_sqrt h3
  have e4 := Real.sq_sqrt h4; have e5 := Real.sq_sqrt h5; have e6 := Real.sq_sqrt h6
  set s := Real.sqrt al; set t := Real.sqrt be; set p := Real.sqrt g0; set p' := Real.sqrt g1
  set q := Real.sqrt g2; set q' := Real.sqrt g3
  rw [← e1, ← e2, ← e3, ← e4, ← e5, ← e6]
  nlinarith [sq_nonneg (s * p' - p * t), sq_nonneg (s * q' - q * t), sq_nonneg (p * q' - q * p')]

theorem g68q_lower (al be u v x y : ℝ) (h1 : 0 ≤ al) (h2 : 0 ≤ be) (g : Noises) (hg : FeasibleNoises u v x y g) :
    twoNoiseValue al be u v x y ≤ rawTwoDet al be g := by
  obtain ⟨hnn, hP, hQ⟩ := hg
  have c := g68q_cs al be (g 0) (g 1) (g 2) (g 3) h1 h2 (hnn 0) (hnn 1) (hnn 2) (hnn 3)
  have hP' := Real.abs_le_sqrt hP
  have hQ' := Real.abs_le_sqrt hQ
  unfold twoNoiseValue rawTwoDet
  refine le_trans ?_ c
  apply pow_le_pow_left₀ (by positivity)
  linarith

theorem g68q_four (g : Noises) (h0 : ∀ i, 0 ≤ g i) (h1 : 1 ≤ g 0 * g 1)
    (h2 : 1 ≤ g 2 * g 3) : 4 ≤ (g 0 + g 2) * (g 1 + g 3) := by
  have c := g68q_cs 0 0 (g 0) (g 1) (g 2) (g 3) le_rfl le_rfl (h0 0) (h0 1) (h0 2) (h0 3)
  have a1 : 1 ≤ Real.sqrt (g 0 * g 1) := by rw [Real.one_le_sqrt]; exact h1
  have a2 : 1 ≤ Real.sqrt (g 2 * g 3) := by rw [Real.one_le_sqrt]; exact h2
  simp only [mul_zero, Real.sqrt_zero, zero_add, add_zero] at c
  nlinarith

theorem g68q_feas (u v x y r : ℝ) (hr : 0 < r) (hu : u = 0) (hx : x = 0) :
    FeasibleNoises u v x y ![r, 1 / r, r, 1 / r] := by
  subst hu hx
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp <;> positivity
  · simp [hr.ne']
  · simp [hr.ne']

theorem g68q_feas' (u v x y r : ℝ) (hr : 0 < r) (hv : v = 0) (hy : y = 0) :
    FeasibleNoises u v x y ![r, 1 / r, r, 1 / r] := by
  subst hv hy
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp <;> positivity
  · simp [hr.ne']
  · simp [hr.ne']

theorem solution (a b c1 c2 d1 d2 u v x y : ℝ)
    (hresource : PhysicalResource (standardCov a b c1 c2))
    (hD : InputOrProcess (!![d1, 0; 0, d2] : QuadratureMatrix)) :
    let al := 2 * d1 + a * u ^ 2 + 2 * c1 * u * x + b * x ^ 2
    let be := 2 * d2 + a * v ^ 2 - 2 * c2 * v * y + b * y ^ 2
    let val := twoNoiseValue al be u v x y
    0 ≤ al ∧ 0 ≤ be ∧
    (∀ g : Noises, FeasibleNoises u v x y g → val ≤ rawTwoDet al be g) ∧
    (∀ eps : ℝ, 0 < eps → ∃ g : Noises,
      FeasibleNoises u v x y g ∧ rawTwoDet al be g < val + eps) ∧
    (0 < al → 0 < be →
      let g : Noises := ![|1 - u * v| * Real.sqrt (al / be),
        |1 - u * v| * Real.sqrt (be / al), |1 - x * y| * Real.sqrt (al / be),
        |1 - x * y| * Real.sqrt (be / al)]
      FeasibleNoises u v x y g ∧ rawTwoDet al be g = val) ∧
    (al = 0 → be = 0 → val = 4 ∧ FeasibleNoises u v x y ![1, 1, 1, 1] ∧
      rawTwoDet al be ![1, 1, 1, 1] = val) ∧
    ((al = 0 ∧ 0 < be) ∨ (0 < al ∧ be = 0) →
      val = 4 ∧ ∀ g : Noises, FeasibleNoises u v x y g →
        val < rawTwoDet al be g) := by
  intro al be val
  obtain ⟨hd1, hd2⟩ := g68q_d_nonneg d1 d2 hD
  have hal0 : (u = 0 ∧ x = 0) ∨ 0 < al := by
    by_cases h : u = 0 ∧ x = 0
    · exact Or.inl h
    · right
      have := g68q_qa a b c1 c2 u x hresource (by tauto)
      simp only [al]; linarith
  have hbe0 : (v = 0 ∧ y = 0) ∨ 0 < be := by
    by_cases h : v = 0 ∧ y = 0
    · exact Or.inl h
    · right
      have := g68q_qb a b c1 c2 v y hresource (by tauto)
      simp only [be]; linarith
  have hal : 0 ≤ al := by
    rcases hal0 with ⟨rfl, rfl⟩ | h
    · simp only [al]; nlinarith
    · exact h.le
  have hbe : 0 ≤ be := by
    rcases hbe0 with ⟨rfl, rfl⟩ | h
    · simp only [be]; nlinarith
    · exact h.le
  have hal_z : al = 0 → u = 0 ∧ x = 0 := fun h => hal0.resolve_right (by rw [h]; exact lt_irrefl 0)
  have hbe_z : be = 0 → v = 0 ∧ y = 0 := fun h => hbe0.resolve_right (by rw [h]; exact lt_irrefl 0)
  -- optimal noises
  have hopt : 0 < al → 0 < be →
      let g : Noises := ![|1 - u * v| * Real.sqrt (al / be),
        |1 - u * v| * Real.sqrt (be / al), |1 - x * y| * Real.sqrt (al / be),
        |1 - x * y| * Real.sqrt (be / al)]
      FeasibleNoises u v x y g ∧ rawTwoDet al be g = val := by
    intro ha hb g
    have es := Real.sq_sqrt ha.le
    have et := Real.sq_sqrt hb.le
    have hs : 0 < Real.sqrt al := Real.sqrt_pos.mpr ha
    have ht : 0 < Real.sqrt be := Real.sqrt_pos.mpr hb
    have r1 : Real.sqrt (al / be) = Real.sqrt al / Real.sqrt be := Real.sqrt_div' _ hb.le
    have r2 : Real.sqrt (be / al) = Real.sqrt be / Real.sqrt al := Real.sqrt_div' _ ha.le
    have r3 : Real.sqrt (al * be) = Real.sqrt al * Real.sqrt be := Real.sqrt_mul ha.le _
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro i; fin_cases i <;> simp [g] <;> positivity
    · simp only [g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, r1, r2]
      rw [show |1 - u * v| * (Real.sqrt al / Real.sqrt be) * (|1 - u * v| * (Real.sqrt be / Real.sqrt al))
        = |1 - u * v| ^ 2 by field_simp, sq_abs]
    · simp only [g, r1, r2]
      simp
      rw [show |1 - x * y| * (Real.sqrt al / Real.sqrt be) * (|1 - x * y| * (Real.sqrt be / Real.sqrt al))
        = |1 - x * y| ^ 2 by field_simp, sq_abs]
    · simp only [rawTwoDet, val, twoNoiseValue, g, r1, r2, r3]
      simp
      generalize Real.sqrt al = s at *
      generalize Real.sqrt be = t at *
      rw [← es, ← et]
      field_simp
      ring
  have hval1 : al = 0 → val = 4 := by
    intro h
    obtain ⟨hu, hx⟩ := hal_z h
    simp only [val, twoNoiseValue, h, zero_mul, Real.sqrt_zero, hu, hx]
    norm_num
  have hval2 : be = 0 → val = 4 := by
    intro h
    obtain ⟨hv, hy⟩ := hbe_z h
    simp only [val, twoNoiseValue, h, mul_zero, Real.sqrt_zero, hv, hy]
    norm_num
  refine ⟨hal, hbe, fun g hg => g68q_lower al be u v x y hal hbe g hg, ?_, hopt, ?_, ?_⟩
  · intro eps heps
    by_cases ha : 0 < al
    · by_cases hb : 0 < be
      · obtain ⟨h1, h2⟩ := hopt ha hb
        exact ⟨_, h1, by rw [h2]; linarith⟩
      · have hb0 : be = 0 := le_antisymm (not_lt.mp hb) hbe
        obtain ⟨hv, hy⟩ := hbe_z hb0
        have hr : 0 < 4 * (al + 1) / eps := by positivity
        refine ⟨_, g68q_feas' u v x y _ hr hv hy, ?_⟩
        rw [hval2 hb0]
        simp only [rawTwoDet, hb0]
        simp
        field_simp
        nlinarith
    · have ha0 : al = 0 := le_antisymm (not_lt.mp ha) hal
      obtain ⟨hu, hx⟩ := hal_z ha0
      have hr : 0 < eps / (4 * (be + 1)) := by positivity
      refine ⟨_, g68q_feas u v x y _ hr hu hx, ?_⟩
      rw [hval1 ha0]
      simp only [rawTwoDet, ha0]
      simp
      field_simp
      nlinarith
  · intro h0 h1
    obtain ⟨hu, hx⟩ := hal_z h0
    refine ⟨hval1 h0, ?_, ?_⟩
    · have := g68q_feas u v x y 1 one_pos hu hx
      simpa using this
    · rw [hval1 h0]
      simp only [rawTwoDet, h0, h1]
      simp [Matrix.cons_val]
      norm_num
  · rintro (⟨h0, hb⟩ | ⟨ha, h0⟩)
    · refine ⟨hval1 h0, fun g hg => ?_⟩
      obtain ⟨hnn, hP, hQ⟩ := hg
      obtain ⟨hu, hx⟩ := hal_z h0
      rw [hu] at hP; rw [hx] at hQ
      simp at hP hQ
      have h4 := g68q_four g hnn hP hQ
      have hg0 : 0 < g 0 := lt_of_le_of_ne (hnn 0) (fun h => by rw [← h] at hP; simp at hP; linarith)
      rw [hval1 h0]
      simp only [rawTwoDet, h0]
      nlinarith [hnn 2, hnn 1, hnn 3]
    · refine ⟨hval2 h0, fun g hg => ?_⟩
      obtain ⟨hnn, hP, hQ⟩ := hg
      obtain ⟨hv, hy⟩ := hbe_z h0
      rw [hv] at hP; rw [hy] at hQ
      simp at hP hQ
      have h4 := g68q_four g hnn hP hQ
      have hg1 : 0 < g 1 := lt_of_le_of_ne (hnn 1) (fun h => by rw [← h] at hP; simp at hP; linarith)
      rw [hval2 h0]
      simp only [rawTwoDet, h0]
      nlinarith [hnn 2, hnn 0, hnn 3]
