-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P50.lemma_28
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:17:14.470968+00:00
-- url     : https://prove2.me/submissions/6ac6e5ee-9284-4948-9e55-fe7e272e1c59

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50
noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set



attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Bridge50.P50

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)






lemma q28_cube (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]

lemma q28_rlog3 (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1) : r * |Real.log r| ^ 3 ≤ 27 := by
  have h := Real.abs_log_mul_self_rpow_lt r ((3 : ℕ)⁻¹ : ℝ) h0 h1 (by norm_num)
  have hp := Real.rpow_inv_natCast_pow h0.le (n := 3) (by norm_num)
  have hnn : 0 ≤ r ^ ((3 : ℕ)⁻¹ : ℝ) := Real.rpow_nonneg h0.le _
  rw [abs_mul, abs_of_nonneg hnn] at h
  norm_num at h
  calc r * |Real.log r| ^ 3 = (|Real.log r| * r ^ ((3 : ℕ)⁻¹ : ℝ)) ^ 3 := by
        rw [mul_pow, hp]; ring
    _ ≤ 3 ^ 3 := by
        apply pow_le_pow_left₀ (by positivity)
        norm_num; linarith
    _ = 27 := by norm_num

lemma q28_rlog (r : ℝ) (h0 : 0 < r) (h1 : r ≤ 1) : r * |Real.log r| ≤ 1 := by
  have h := Real.abs_log_mul_self_lt r h0 h1
  rw [abs_mul, abs_of_pos h0] at h
  linarith

/-- generic bound for the classical third moment -/
lemma q28_generic {A J : Type*} [Fintype A] (r : A → ℝ) (s : A → J) (sv : J → ℝ) (c : A → ℝ)
    [Fintype J]
    (hr0 : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a ≤ 1) (hc0 : ∀ a, 0 ≤ c a) (hc1 : ∀ a, c a ≤ 1) :
    classicalT (fun a => r a * c a) (fun a => sv (s a) * c a) ≤
      Fintype.card A * (4 * (27 * (1 / Real.log 2) ^ 3 +
        ((∑ j, |Real.log (sv j)| / Real.log 2) +
          Fintype.card A * (1 / Real.log 2 + ∑ j, |Real.log (sv j)| / Real.log 2)) ^ 3)) := by
  set K := ∑ j, |Real.log (sv j)| / Real.log 2 with hK
  set α := 1 / Real.log 2 with hα
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hαpos : 0 < α := by positivity
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun j _ => by positivity)
  have hKj : ∀ j, |Real.log (sv j)| / Real.log 2 ≤ K := fun j =>
    Finset.single_le_sum (f := fun j => |Real.log (sv j)| / Real.log 2)
      (fun j _ => by positivity) (Finset.mem_univ j)
  set P := fun a => r a * c a with hP
  set Q := fun a => sv (s a) * c a with hQ
  -- bound on the log-likelihood ratio
  have hL : ∀ a, P a ≠ 0 → |logTwo (P a / Q a)| ≤ α * |Real.log (r a)| + K := by
    intro a ha
    have hra : r a ≠ 0 := fun h => ha (by simp [hP, h])
    have hca : c a ≠ 0 := fun h => ha (by simp [hP, h])
    have e : P a / Q a = r a / sv (s a) := by
      simp only [hP, hQ]; rw [mul_div_mul_right _ _ hca]
    rw [e]
    unfold logTwo
    rw [abs_div, abs_of_pos hl2]
    have hlog : |Real.log (r a / sv (s a))| ≤ |Real.log (r a)| + |Real.log (sv (s a))| := by
      by_cases hs : sv (s a) = 0
      · simp [hs]
      · rw [Real.log_div hra hs]; exact abs_sub _ _
    have := hKj (s a)
    calc |Real.log (r a / sv (s a))| / Real.log 2
        ≤ (|Real.log (r a)| + |Real.log (sv (s a))|) / Real.log 2 :=
          div_le_div_of_nonneg_right hlog hl2.le
      _ = α * |Real.log (r a)| + |Real.log (sv (s a))| / Real.log 2 := by
          rw [hα]; ring
      _ ≤ α * |Real.log (r a)| + K := by linarith
  have hP0 : ∀ a, 0 ≤ P a := fun a => mul_nonneg (hr0 a) (hc0 a)
  have hPr : ∀ a, P a ≤ r a := fun a => by
    simp only [hP]; nlinarith [hr0 a, hc0 a, hc1 a]
  have hrpos : ∀ a, P a ≠ 0 → 0 < r a := fun a ha =>
    lt_of_le_of_ne (hr0 a) (fun h => ha (by simp [hP, ← h]))
  -- bound on each |P L|
  have hPL : ∀ a, |P a * logTwo (P a / Q a)| ≤ α + K := by
    intro a
    by_cases ha : P a = 0
    · simp [ha]; positivity
    · rw [abs_mul, abs_of_nonneg (hP0 a)]
      have h1 := hL a ha
      have h2 := q28_rlog (r a) (hrpos a ha) (hr1 a)
      calc P a * |logTwo (P a / Q a)| ≤ r a * (α * |Real.log (r a)| + K) :=
            mul_le_mul (hPr a) h1 (abs_nonneg _) (hr0 a)
        _ = α * (r a * |Real.log (r a)|) + r a * K := by ring
        _ ≤ α * 1 + 1 * K := by
            gcongr
            · exact hr1 a
        _ = α + K := by ring
  set M0 := (Fintype.card A : ℝ) * (α + K) with hM0
  have hD0 : 0 ≤ (nsClassicalD P Q).toReal := ENNReal.toReal_nonneg
  have hD : (nsClassicalD P Q).toReal ≤ M0 := by
    unfold nsClassicalD
    split_ifs
    · rw [ENNReal.toReal_ofReal']
      apply max_le _ (by positivity)
      calc ∑ a, P a * logTwo (P a / Q a) ≤ ∑ a, |P a * logTwo (P a / Q a)| :=
            Finset.sum_le_sum (fun a _ => le_abs_self _)
        _ ≤ ∑ _a : A, (α + K) := Finset.sum_le_sum (fun a _ => hPL a)
        _ = M0 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hM0]
    · simp; positivity
  unfold classicalT
  have hterm : ∀ a, P a * |logTwo (P a / Q a) - (nsClassicalD P Q).toReal| ^ 3 ≤
      4 * (27 * α ^ 3 + (K + M0) ^ 3) := by
    intro a
    by_cases ha : P a = 0
    · rw [ha, zero_mul]; positivity
    · have hra := hrpos a ha
      have h1 := hL a ha
      have hb : |logTwo (P a / Q a) - (nsClassicalD P Q).toReal| ≤
          α * |Real.log (r a)| + (K + M0) := by
        have := abs_sub (logTwo (P a / Q a)) (nsClassicalD P Q).toReal
        rw [abs_of_nonneg hD0] at this
        linarith
      have hx : 0 ≤ α * |Real.log (r a)| := by positivity
      have hy : 0 ≤ K + M0 := by positivity
      calc P a * |logTwo (P a / Q a) - (nsClassicalD P Q).toReal| ^ 3
          ≤ r a * (α * |Real.log (r a)| + (K + M0)) ^ 3 :=
            mul_le_mul (hPr a) (pow_le_pow_left₀ (abs_nonneg _) hb 3) (by positivity) (hr0 a)
        _ ≤ r a * (4 * ((α * |Real.log (r a)|) ^ 3 + (K + M0) ^ 3)) :=
            mul_le_mul_of_nonneg_left (q28_cube _ _ hx hy) (hr0 a)
        _ = 4 * (α ^ 3 * (r a * |Real.log (r a)| ^ 3) + r a * (K + M0) ^ 3) := by ring
        _ ≤ 4 * (α ^ 3 * 27 + 1 * (K + M0) ^ 3) := by
            gcongr
            · exact q28_rlog3 _ hra (hr1 a)
            · exact hr1 a
        _ = 4 * (27 * α ^ 3 + (K + M0) ^ 3) := by ring
  calc ∑ a, P a * |logTwo (P a / Q a) - (nsClassicalD P Q).toReal| ^ 3
      ≤ ∑ _a : A, 4 * (27 * α ^ 3 + (K + M0) ^ 3) := Finset.sum_le_sum (fun a _ => hterm a)
    _ = _ := by simp [hM0]

lemma q28_eig_le_one {I : Type*} [Fintype I] [DecidableEq I] {rho : Mat I}
    (h : QAlgorithms.IsDensityMatrix rho) (hH : rho.IsHermitian) (i : I) :
    0 ≤ hH.eigenvalues i ∧ hH.eigenvalues i ≤ 1 := by
  have h0 : ∀ j, 0 ≤ hH.eigenvalues j := fun j => h.1.eigenvalues_nonneg j
  refine ⟨h0 i, ?_⟩
  have htr := hH.trace_eq_sum_eigenvalues
  rw [h.2] at htr
  have hs : ∑ j, hH.eigenvalues j = 1 := by
    have := congrArg Complex.re htr
    simpa using this.symm
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

lemma q28_overlap {I : Type*} [Fintype I] (u v : EuclideanSpace ℂ I) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Complex.normSq (∑ k, conj (u k) * v k) ≤ 1 := by
  have e : (∑ k, conj (u k) * v k) = inner ℂ u v := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp [mul_comm]
  rw [e, Complex.normSq_eq_norm_sq]
  have := norm_inner_le_norm (𝕜 := ℂ) u v
  rw [hu, hv] at this
  have h0 := norm_nonneg (inner ℂ u v)
  nlinarith

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ∀ rho ∈ S, QAlgorithms.IsDensityMatrix rho)
    (sigma : Mat I) (hsigma : QAlgorithms.IsDensityMatrix sigma) (hpos : 0 < minEigenvalue sigma) :
    ∃ T : ℝ, ∀ rho ∈ S, thirdMoment rho sigma ≤ T := by
  have hsH : sigma.IsHermitian := hsigma.1.isHermitian
  let sv : I → ℝ := hsH.eigenvalues
  refine ⟨Fintype.card (I × I) * (4 * (27 * (1 / Real.log 2) ^ 3 +
        ((∑ j, |Real.log (sv j)| / Real.log 2) +
          Fintype.card (I × I) * (1 / Real.log 2 + ∑ j, |Real.log (sv j)| / Real.log 2)) ^ 3)), ?_⟩
  intro rho hrho
  have hd := hS rho hrho
  have hH : rho.IsHermitian := hd.1.isHermitian
  unfold thirdMoment nsP nsQ canonicalSpectral
  rw [dif_pos hH, dif_pos hsH]
  exact q28_generic (A := I × I) (fun a => hH.eigenvalues a.1) (fun a => a.2) sv
    (fun a => Complex.normSq (∑ k, conj (hH.eigenvectorBasis a.1 k) * hsH.eigenvectorBasis a.2 k))
    (fun a => (q28_eig_le_one hd hH a.1).1) (fun a => (q28_eig_le_one hd hH a.1).2)
    (fun a => Complex.normSq_nonneg _)
    (fun a => q28_overlap _ _ (hH.eigenvectorBasis.orthonormal.1 a.1)
      (hsH.eigenvectorBasis.orthonormal.1 a.2))
