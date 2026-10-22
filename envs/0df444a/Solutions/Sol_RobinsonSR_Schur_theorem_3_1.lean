-- Prove2me | solution 1 for RobinsonSR.Schur.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:40:22.124427+00:00
-- url     : https://prove2.me/submissions/1e71543b-7f30-46f7-acf3-b7a335bf3451

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting



namespace RobinsonSR.Schur

open scoped RealInnerProductSpace Matrix
open WithLp

lemma g_tel {m n : Type*} [Fintype n] [DecidableEq n] (M : Matrix m n ℝ) (v : EuclideanSpace ℝ n) :
    M.toEuclideanLin v = toLp 2 (M *ᵥ ofLp v) := rfl

def g_join {r s : ℕ} (a : EuclideanSpace ℝ (Fin r)) (b : EuclideanSpace ℝ (Fin s)) :
    EuclideanSpace ℝ (Fin r ⊕ Fin s) := toLp 2 (Sum.elim (ofLp a) (ofLp b))

lemma g_upper_join {r s : ℕ} (a : EuclideanSpace ℝ (Fin r)) (b : EuclideanSpace ℝ (Fin s)) :
    upperBlock (g_join a b) = a := rfl
lemma g_lower_join {r s : ℕ} (a : EuclideanSpace ℝ (Fin r)) (b : EuclideanSpace ℝ (Fin s)) :
    lowerBlock (g_join a b) = b := rfl

lemma g_upper_sub {r s : ℕ} (a b : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    upperBlock (a - b) = upperBlock a - upperBlock b := rfl
lemma g_lower_sub {r s : ℕ} (a b : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    lowerBlock (a - b) = lowerBlock a - lowerBlock b := rfl

lemma g_inner_split {r s : ℕ} (u v : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    ⟪u, v⟫ = ⟪upperBlock u, upperBlock v⟫ + ⟪lowerBlock u, lowerBlock v⟫ := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, upperBlock, lowerBlock]

lemma g_nc_prod {r s : ℕ} (K : Set (EuclideanSpace ℝ (Fin s))) (v w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    v ∈ normalCone (prodSet K) w ↔ upperBlock v = 0 ∧ lowerBlock v ∈ normalCone K (lowerBlock w) := by
  constructor
  · rintro ⟨hw, h⟩
    have h1 := h (g_join (upperBlock w + upperBlock v) (lowerBlock w)) (by
      show lowerBlock (g_join _ _) ∈ K
      rw [g_lower_join]; exact hw)
    rw [g_inner_split, g_upper_sub, g_lower_sub, g_upper_join, g_lower_join] at h1
    simp only [add_sub_cancel_left, sub_self, inner_zero_right, add_zero] at h1
    refine ⟨?_, hw, fun c hc => ?_⟩
    · have : ‖upperBlock v‖ ^ 2 ≤ 0 := by rw [← real_inner_self_eq_norm_sq]; exact h1
      have : ‖upperBlock v‖ = 0 := by nlinarith [norm_nonneg (upperBlock v)]
      exact norm_eq_zero.mp this
    · have h2 := h (g_join (upperBlock w) c) (by
        show lowerBlock (g_join _ _) ∈ K
        rw [g_lower_join]; exact hc)
      rw [g_inner_split, g_upper_sub, g_lower_sub, g_upper_join, g_lower_join] at h2
      simpa using h2
  · rintro ⟨h0, hw, h⟩
    refine ⟨hw, fun c hc => ?_⟩
    rw [g_inner_split, h0, g_lower_sub]
    simpa using h _ hc

lemma g_upper_A {r s : ℕ} (A₁₁ : Matrix (Fin r) (Fin r) ℝ) (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ) (A₂₂ : Matrix (Fin s) (Fin s) ℝ) (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    upperBlock ((Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin w) =
      A₁₁.toEuclideanLin (upperBlock w) + A₁₂.toEuclideanLin (lowerBlock w) := by
  ext i
  simp [g_tel, upperBlock, lowerBlock, Matrix.fromBlocks_mulVec]
  rfl

lemma g_lower_A {r s : ℕ} (A₁₁ : Matrix (Fin r) (Fin r) ℝ) (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ) (A₂₂ : Matrix (Fin s) (Fin s) ℝ) (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    lowerBlock ((Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin w) =
      A₂₁.toEuclideanLin (upperBlock w) + A₂₂.toEuclideanLin (lowerBlock w) := by
  ext i
  simp [g_tel, upperBlock, lowerBlock, Matrix.fromBlocks_mulVec]
  rfl


lemma g_inv_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (x b : EuclideanSpace ℝ (Fin n)) :
    A.toEuclideanLin x = b ↔ x = (A⁻¹).toEuclideanLin b := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  constructor
  · rintro rfl
    simp only [g_tel, ofLp_toLp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  · rintro rfl
    simp only [g_tel, ofLp_toLp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

lemma g_schur_lin {r s : ℕ} (A₁₁ : Matrix (Fin r) (Fin r) ℝ) (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ) (A₂₂ : Matrix (Fin s) (Fin s) ℝ) (x : EuclideanSpace ℝ (Fin s)) :
    (schur A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin x =
      A₂₂.toEuclideanLin x - A₂₁.toEuclideanLin ((A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin x)) := by
  simp only [g_tel, ofLp_toLp, schur, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rfl

theorem inclusion_core (r s : ℕ)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (hA₁₁ : A₁₁.det ≠ 0) (K : Set (EuclideanSpace ℝ (Fin s)))
    (y w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    (y - (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin w ∈
      normalCone (prodSet K) w) ↔
    (upperBlock w = (A₁₁⁻¹).toEuclideanLin (upperBlock y) -
      (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (lowerBlock w))) ∧
    (lowerBlock y - A₂₁.toEuclideanLin ((A₁₁⁻¹).toEuclideanLin (upperBlock y)) -
      (schur A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin (lowerBlock w) ∈
      normalCone K (lowerBlock w)) := by
  rw [g_nc_prod, g_upper_sub, g_lower_sub, g_upper_A, g_lower_A]
  have key : upperBlock y - (A₁₁.toEuclideanLin (upperBlock w) + A₁₂.toEuclideanLin (lowerBlock w)) = 0 ↔
      upperBlock w = (A₁₁⁻¹).toEuclideanLin (upperBlock y) -
        (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (lowerBlock w)) := by
    rw [sub_eq_zero, eq_comm, ← eq_sub_iff_add_eq, g_inv_iff _ hA₁₁, map_sub]
  rw [key]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    convert h2 using 1
    rw [h1, map_sub, g_schur_lin]; abel
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    convert h2 using 1
    rw [h1, map_sub, g_schur_lin]; abel


open scoped RealInnerProductSpace Matrix

/-- metric projection onto a nonempty closed convex set -/
lemma g_proj_exists {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hne : K.Nonempty)
    (hcl : IsClosed K) (hcv : Convex ℝ K) :
    ∃ P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ∀ x, P x ∈ K ∧ ∀ z ∈ K, ⟪x - P x, z - P x⟫ ≤ 0 := by
  have : ∀ x : EuclideanSpace ℝ (Fin n), ∃ p, p ∈ K ∧ ∀ z ∈ K, ⟪x - p, z - p⟫ ≤ 0 := by
    intro x
    obtain ⟨v, hv, heq⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv x
    exact ⟨v, hv, (norm_eq_iInf_iff_real_inner_le_zero hcv hv).mp heq⟩
  choose P hP using this
  exact ⟨P, fun x => ⟨(hP x).1, (hP x).2⟩⟩

lemma g_proj_nonexp {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : ∀ x, P x ∈ K ∧ ∀ z ∈ K, ⟪x - P x, z - P x⟫ ≤ 0) (x x' : EuclideanSpace ℝ (Fin n)) :
    ‖P x - P x'‖ ≤ ‖x - x'‖ := by
  have h1 := (hP x).2 (P x') (hP x').1
  have h2 := (hP x').2 (P x) (hP x).1
  have key : ‖P x - P x'‖ ^ 2 ≤ ⟪x - x', P x - P x'⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm] at h1 h2 ⊢
    linarith
  have hb := real_inner_le_norm (x - x') (P x - P x')
  nlinarith [norm_nonneg (P x - P x'), norm_nonneg (x - x')]

lemma g_vi_exists {n : ℕ} (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (c : ℝ) (hc : 0 < c) (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, T x⟫)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hne : K.Nonempty)
    (hcl : IsClosed K) (hcv : Convex ℝ K) (y : EuclideanSpace ℝ (Fin n)) :
    ∃ w ∈ K, ∀ z ∈ K, ⟪y - T w, z - w⟫ ≤ 0 := by
  obtain ⟨P, hP⟩ := g_proj_exists K hne hcl hcv
  set B : ℝ := ‖T‖ ^ 2 + c ^ 2 with hB
  have hB0 : 0 < B := by positivity
  set α : ℝ := c / B with hα
  have hα0 : 0 < α := div_pos hc hB0
  set q : ℝ := 1 - c ^ 2 / B with hq
  have hq0 : 0 ≤ q := by
    rw [hq, sub_nonneg, div_le_one hB0]; nlinarith [sq_nonneg ‖T‖]
  have hq1 : q < 1 := by
    rw [hq]; have : 0 < c ^ 2 / B := by positivity
    linarith
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun w => P (w - α • (T w - y))
  have hstep : ∀ d : EuclideanSpace ℝ (Fin n), ‖d - α • T d‖ ≤ Real.sqrt q * ‖d‖ := by
    intro d
    have h1 : ‖d - α • T d‖ ^ 2 ≤ q * ‖d‖ ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hα0]
      have hTd : ‖T d‖ ≤ ‖T‖ * ‖d‖ := T.le_opNorm d
      have hTd2 : ‖T d‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖d‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hTd 2
      have hcd := hT d
      have e1 : α * ‖T d‖ * (α * ‖T d‖) ≤ α ^ 2 * (B * ‖d‖ ^ 2) := by
        have : ‖T d‖ ^ 2 ≤ B * ‖d‖ ^ 2 := by nlinarith [sq_nonneg c, sq_nonneg ‖d‖]
        nlinarith [sq_nonneg α]
      have e2 : α ^ 2 * B = c ^ 2 / B := by rw [hα]; field_simp
      have e3 : 2 * (α * ⟪d, T d⟫) ≥ 2 * α * c * ‖d‖ ^ 2 := by nlinarith
      have e4 : α * c = c ^ 2 / B := by rw [hα]; field_simp
      rw [hq]
      nlinarith [sq_nonneg ‖d‖]
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hq0, Real.sqrt_sq (norm_nonneg _)] at this
  have hlip : LipschitzWith ⟨Real.sqrt q, Real.sqrt_nonneg _⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro w w'
    simp only [dist_eq_norm, NNReal.coe_mk, F]
    refine (g_proj_nonexp K P hP _ _).trans ?_
    have : w - α • (T w - y) - (w' - α • (T w' - y)) = (w - w') - α • T (w - w') := by
      rw [map_sub, smul_sub, smul_sub, smul_sub]; abel
    rw [this]; exact hstep _
  have hcon : ContractingWith ⟨Real.sqrt q, Real.sqrt_nonneg _⟩ F := by
    refine ⟨?_, hlip⟩
    show Real.sqrt q < 1
    rw [Real.sqrt_lt' one_pos]; simpa using hq1
  set w := ContractingWith.fixedPoint F hcon
  have hw : F w = w := ContractingWith.fixedPoint_isFixedPt hcon
  refine ⟨w, hw ▸ (hP _).1, fun z hz => ?_⟩
  have h := (hP (w - α • (T w - y))).2 z hz
  change ⟪w - α • (T w - y) - F w, z - F w⟫ ≤ 0 at h
  rw [hw] at h
  have : w - α • (T w - y) - w = α • (y - T w) := by
    rw [smul_sub, smul_sub]; abel
  rw [this, inner_smul_left] at h
  simp only [conj_trivial] at h
  by_contra hcon'
  push_neg at hcon'
  nlinarith


lemma g_est {n : ℕ} (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (c : ℝ) (hc : 0 < c) (hT : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, T x⟫)
    (K : Set (EuclideanSpace ℝ (Fin n))) (y1 y2 w1 w2 : EuclideanSpace ℝ (Fin n))
    (hw1 : w1 ∈ K) (hw2 : w2 ∈ K)
    (h1 : ∀ z ∈ K, ⟪y1 - T w1, z - w1⟫ ≤ 0) (h2 : ∀ z ∈ K, ⟪y2 - T w2, z - w2⟫ ≤ 0) :
    c * ‖w1 - w2‖ ≤ ‖y1 - y2‖ := by
  have a := h1 w2 hw2
  have b := h2 w1 hw1
  have hd := hT (w1 - w2)
  have hb := real_inner_le_norm (y1 - y2) (w1 - w2)
  have key : c * ‖w1 - w2‖ ^ 2 ≤ ⟪y1 - y2, w1 - w2⟫ := by
    rw [map_sub] at hd
    simp only [inner_sub_left, inner_sub_right, real_inner_comm] at a b hd ⊢
    linarith
  nlinarith [norm_nonneg (w1 - w2), norm_nonneg (y1 - y2)]

lemma g_inner_dot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, M.toEuclideanLin x⟫ = ofLp x ⬝ᵥ (M *ᵥ ofLp x) := by
  simp [PiLp.inner_apply, g_tel, dotProduct, mul_comm]

lemma g_coercive {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (hM : PosDefNS M) :
    ∃ c > 0, ∀ x : EuclideanSpace ℝ (Fin n), c * ‖x‖ ^ 2 ≤ ⟪x, M.toEuclideanLin x⟫ := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ⟪x, M.toEuclideanLin x⟫
  have hf : Continuous f := by
    have : Continuous (LinearMap.toContinuousLinearMap M.toEuclideanLin) :=
      (LinearMap.toContinuousLinearMap M.toEuclideanLin).continuous
    exact continuous_id.inner this
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn hne
    hf.continuousOn
  have hx0n : ‖x0‖ = 1 := by simpa using hx0
  have hx0ne : ofLp x0 ≠ 0 := by
    intro h
    have : x0 = 0 := by
      have := congrArg (toLp 2) h
      simpa using this
    rw [this] at hx0n; simp at hx0n
  refine ⟨f x0, ?_, fun x => ?_⟩
  · show 0 < ⟪x0, M.toEuclideanLin x0⟫
    rw [g_inner_dot]; exact hM _ hx0ne
  · by_cases hx : x = 0
    · subst hx; simp
    · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      set u := ‖x‖⁻¹ • x with hu
      have hus : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simp [hu, norm_smul, hxn.ne']
      have hle : f x0 ≤ f u := hmin hus
      have hfu : f u = ‖x‖⁻¹ ^ 2 * f x := by
        simp only [f, hu, map_smul, inner_smul_left, inner_smul_right, conj_trivial]; ring
      rw [hfu] at hle
      have : ‖x‖ ^ 2 * ‖x‖⁻¹ ^ 2 = 1 := by field_simp
      calc f x0 * ‖x‖ ^ 2 ≤ ‖x‖⁻¹ ^ 2 * f x * ‖x‖ ^ 2 := by gcongr
        _ = f x := by rw [mul_comm, ← mul_assoc, this, one_mul]

theorem smono_core (s : ℕ) (hs : 0 < s)
    (M : Matrix (Fin s) (Fin s) ℝ)
    (K : Set (EuclideanSpace ℝ (Fin s)))
    (hK₁ : K.Nonempty) (hK₂ : IsClosed K) (hK₃ : Convex ℝ K)
    (hM : PosDefNS M) :
    InvIsLipschitzFunction M K := by
  obtain ⟨c, hc, hT⟩ := g_coercive hs M hM
  let T := LinearMap.toContinuousLinearMap M.toEuclideanLin
  have hTe : ∀ x, T x = M.toEuclideanLin x := fun x => rfl
  have hT' : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, T x⟫ := fun x => by rw [hTe]; exact hT x
  choose σ hσK hσ using fun y => g_vi_exists T c hc hT' K hK₁ hK₂ hK₃ y
  simp only [hTe] at hσ
  refine ⟨1 / c, σ, fun y => ⟨⟨hσK y, hσ y⟩, fun w hw => ?_⟩, fun y1 y2 => ?_⟩
  · have := g_est M.toEuclideanLin c hc hT K y y w (σ y) hw.1 (hσK y) hw.2 (hσ y)
    simp only [sub_self, norm_zero] at this
    have h0 : ‖w - σ y‖ = 0 := by nlinarith [norm_nonneg (w - σ y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  · have := g_est M.toEuclideanLin c hc hT K y1 y2 (σ y1) (σ y2) (hσK y1) (hσK y2) (hσ y1) (hσ y2)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
    linarith


lemma g_eta {r s : ℕ} (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    w = g_join (upperBlock w) (lowerBlock w) := by
  ext i; cases i <;> rfl

lemma g_norm_sq {r s : ℕ} (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    ‖w‖ ^ 2 = ‖upperBlock w‖ ^ 2 + ‖lowerBlock w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    g_inner_split]

lemma g_norm_upper {r s : ℕ} (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    ‖upperBlock w‖ ≤ ‖w‖ := by
  have := g_norm_sq w
  nlinarith [norm_nonneg w, norm_nonneg (upperBlock w), norm_nonneg (lowerBlock w)]

lemma g_norm_lower {r s : ℕ} (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    ‖lowerBlock w‖ ≤ ‖w‖ := by
  have := g_norm_sq w
  nlinarith [norm_nonneg w, norm_nonneg (upperBlock w), norm_nonneg (lowerBlock w)]

lemma g_norm_join {r s : ℕ} (a : EuclideanSpace ℝ (Fin r)) (b : EuclideanSpace ℝ (Fin s)) :
    ‖g_join a b‖ ≤ ‖a‖ + ‖b‖ := by
  have := g_norm_sq (g_join a b)
  rw [g_upper_join, g_lower_join] at this
  nlinarith [norm_nonneg (g_join a b), norm_nonneg a, norm_nonneg b]

lemma g_join_sub {r s : ℕ} (a a' : EuclideanSpace ℝ (Fin r)) (b b' : EuclideanSpace ℝ (Fin s)) :
    g_join a b - g_join a' b' = g_join (a - a') (b - b') := by
  ext i; cases i <;> rfl

lemma g_bound {m n : ℕ} (N : Matrix (Fin m) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖N.toEuclideanLin x‖ ≤ C * ‖x‖ :=
  ⟨‖LinearMap.toContinuousLinearMap N.toEuclideanLin‖, norm_nonneg _,
    fun x => (LinearMap.toContinuousLinearMap N.toEuclideanLin).le_opNorm x⟩

theorem block_core (r s : ℕ)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (hA₁₁ : A₁₁.det ≠ 0) (K : Set (EuclideanSpace ℝ (Fin s)))
    (h : InvIsLipschitzFunction (schur A₁₁ A₁₂ A₂₁ A₂₂) K) :
    InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (prodSet K) := by
  obtain ⟨L, τ, hτ, hL⟩ := h
  set L' := max L 0
  have hL' : ∀ a b, ‖τ a - τ b‖ ≤ L' * ‖a - b‖ := fun a b =>
    (hL a b).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hL'0 : 0 ≤ L' := le_max_right _ _
  obtain ⟨C1, hC1, hB1⟩ := g_bound (A₁₁⁻¹)
  obtain ⟨C2, hC2, hB2⟩ := g_bound A₁₂
  obtain ⟨C3, hC3, hB3⟩ := g_bound A₂₁
  let R : EuclideanSpace ℝ (Fin r ⊕ Fin s) → EuclideanSpace ℝ (Fin s) := fun y =>
    lowerBlock y - A₂₁.toEuclideanLin ((A₁₁⁻¹).toEuclideanLin (upperBlock y))
  let σ : EuclideanSpace ℝ (Fin r ⊕ Fin s) → EuclideanSpace ℝ (Fin r ⊕ Fin s) := fun y =>
    g_join ((A₁₁⁻¹).toEuclideanLin (upperBlock y) -
      (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (τ (R y)))) (τ (R y))
  have hRsub : ∀ y1 y2, R y1 - R y2 = R (y1 - y2) := by
    intro y1 y2
    simp only [R, g_upper_sub, g_lower_sub, map_sub]; abel
  have hR : ∀ y, ‖R y‖ ≤ (1 + C3 * C1) * ‖y‖ := by
    intro y
    have e1 := norm_sub_le (lowerBlock y) (A₂₁.toEuclideanLin ((A₁₁⁻¹).toEuclideanLin (upperBlock y)))
    have e2 := hB3 ((A₁₁⁻¹).toEuclideanLin (upperBlock y))
    have e3 := hB1 (upperBlock y)
    have e4 := g_norm_upper y
    have e5 := g_norm_lower y
    have : C3 * ‖(A₁₁⁻¹).toEuclideanLin (upperBlock y)‖ ≤ C3 * (C1 * ‖y‖) :=
      mul_le_mul_of_nonneg_left (e3.trans (mul_le_mul_of_nonneg_left e4 hC1)) hC3
    show ‖R y‖ ≤ _
    simp only [R]
    nlinarith
  refine ⟨C1 + C1 * C2 * (L' * (1 + C3 * C1)) + L' * (1 + C3 * C1), σ, fun y => ⟨?_, fun w hw => ?_⟩,
    fun y1 y2 => ?_⟩
  · rw [inclusion_core r s A₁₁ A₁₂ A₂₁ A₂₂ hA₁₁ K, g_upper_join, g_lower_join]
    exact ⟨rfl, (hτ (R y)).1⟩
  · rw [inclusion_core r s A₁₁ A₁₂ A₂₁ A₂₂ hA₁₁ K] at hw
    have h2 : lowerBlock w = τ (R y) := (hτ (R y)).2 _ hw.2
    rw [g_eta w, hw.1, h2]
  · have hτd : ‖τ (R y1) - τ (R y2)‖ ≤ L' * (1 + C3 * C1) * ‖y1 - y2‖ := by
      refine (hL' _ _).trans ?_
      rw [hRsub, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hR _) hL'0
    simp only [σ]
    rw [g_join_sub]
    refine (g_norm_join _ _).trans ?_
    have hu : ‖(A₁₁⁻¹).toEuclideanLin (upperBlock y1) - (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (τ (R y1))) -
        ((A₁₁⁻¹).toEuclideanLin (upperBlock y2) - (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (τ (R y2))))‖
        ≤ C1 * ‖y1 - y2‖ + C1 * C2 * (L' * (1 + C3 * C1) * ‖y1 - y2‖) := by
      have : (A₁₁⁻¹).toEuclideanLin (upperBlock y1) - (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (τ (R y1))) -
        ((A₁₁⁻¹).toEuclideanLin (upperBlock y2) - (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (τ (R y2)))) =
        (A₁₁⁻¹).toEuclideanLin (upperBlock (y1 - y2)) -
          (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (τ (R y1) - τ (R y2))) := by
        rw [g_upper_sub]; simp only [map_sub]; abel
      rw [this]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · exact (hB1 _).trans (mul_le_mul_of_nonneg_left (g_norm_upper _) hC1)
      · refine (hB1 _).trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left ((hB2 _).trans (mul_le_mul_of_nonneg_left hτd hC2)) hC1
    nlinarith

theorem nonsingular_core (r s : ℕ)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (h : InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)
      (prodSet (nonnegOrthant s))) :
    A₁₁.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A₁₁)).mpr hdet
  obtain ⟨L, σ, hσ, -⟩ := h
  set C : ℝ := ∑ j, |(A₂₁ *ᵥ v) j| with hC
  have hCj : ∀ j, |(A₂₁ *ᵥ v) j| ≤ C := fun j =>
    Finset.single_le_sum (f := fun j => |(A₂₁ *ᵥ v) j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  let y : EuclideanSpace ℝ (Fin r ⊕ Fin s) := g_join 0 (toLp 2 (fun _ => -C))
  have hsol : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      y - (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin (g_join (toLp 2 (t • v)) 0) ∈
        normalCone (prodSet (nonnegOrthant s)) (g_join (toLp 2 (t • v)) 0) := by
    intro t ht0 ht1
    rw [g_nc_prod, g_upper_sub, g_lower_sub, g_upper_A, g_lower_A]
    simp only [g_upper_join, g_lower_join]
    refine ⟨?_, ?_, ?_⟩
    · ext i
      simp only [y, g_upper_join, g_tel, map_zero, add_zero, Matrix.mulVec_smul, hv, ofLp_toLp, smul_zero,
        sub_zero, PiLp.zero_apply, PiLp.sub_apply]
      simp
    · intro j; simp
    · intro c hc
      rw [PiLp.inner_apply]
      apply Finset.sum_nonpos
      intro j _
      have hcj : 0 ≤ c j := hc j
      have hb : -C - t * (A₂₁ *ᵥ v) j ≤ 0 := by
        have := hCj j
        have h2 : -(A₂₁ *ᵥ v) j ≤ |(A₂₁ *ᵥ v) j| := neg_le_abs _
        have h3 : (A₂₁ *ᵥ v) j ≤ |(A₂₁ *ᵥ v) j| := le_abs_self _
        rcases le_total 0 ((A₂₁ *ᵥ v) j) with h | h
        · nlinarith
        · nlinarith
      simp [y, g_join, lowerBlock, g_tel, Matrix.mulVec_smul]
      nlinarith
  have e0 := (hσ y).2 _ (hsol 0 le_rfl zero_le_one)
  have e1 := (hσ y).2 _ (hsol 1 zero_le_one le_rfl)
  have := congrArg upperBlock (e0.trans e1.symm)
  rw [g_upper_join, g_upper_join] at this
  apply hv0
  have := congrArg ofLp this
  simpa using this.symm


def g_NSR {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, x ≠ 0 → ∃ i, 0 < x i * (M *ᵥ x) i

def g_P {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (f : κ → ι), Function.Injective f →
    0 < (M.submatrix f f).det

lemma g_det_minor {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℝ) (k : κ) :
    (B.updateRow k (Pi.single k 1)).det =
      (B.submatrix (fun j : {j // j ≠ k} => (j : κ)) (fun j : {j // j ≠ k} => (j : κ))).det := by
  set C := B.updateRow k (Pi.single k 1)
  let e := Equiv.sumCompl (fun j : κ => j = k)
  rw [← Matrix.det_submatrix_equiv_self e C, ← Matrix.fromBlocks_toBlocks (C.submatrix e e)]
  have h12 : (C.submatrix e e).toBlocks₁₂ = 0 := by
    ext a b
    have ha : (a : κ) = k := a.2
    have hb : (b : κ) ≠ k := b.2
    simp [Matrix.toBlocks₁₂, C, e, ha, Pi.single_apply, hb]
  rw [h12, Matrix.det_fromBlocks_zero₁₂]
  have h11 : ((C.submatrix e e).toBlocks₁₁).det = 1 := by
    haveI : Unique {j : κ // j = k} := ⟨⟨⟨k, rfl⟩⟩, fun a => Subtype.ext a.2⟩
    rw [Matrix.det_unique]
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply]
    have hd : e (Sum.inl default) = k := (default : {j // j = k}).2
    rw [hd]
    simp [C]
  rw [h11, one_mul]
  congr 1
  ext a b
  have ha : (a : κ) ≠ k := a.2
  simp [Matrix.toBlocks₂₂, C, e, ha]

lemma g_det_update {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℝ) (k : κ) (c : ℝ) :
    (B + Matrix.diagonal (Pi.single k c)).det =
      B.det + c * (B.submatrix (fun j : {j // j ≠ k} => (j : κ)) (fun j : {j // j ≠ k} => (j : κ))).det := by
  have : B + Matrix.diagonal (Pi.single k c) = B.updateRow k (B k + c • Pi.single k 1) := by
    ext i j
    by_cases hi : i = k
    · subst hi; simp [Matrix.diagonal_apply, Pi.single_apply, eq_comm]
    · simp [Matrix.diagonal_apply, Pi.single_apply, hi, Matrix.updateRow_ne hi]
  rw [this, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, g_det_minor]

lemma g_P_update {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : g_P A) (k : ι) (c : ℝ)
    (hc : 0 ≤ c) : g_P (A + Matrix.diagonal (Pi.single k c)) := by
  intro κ _ _ f hf
  have hsub : (A + Matrix.diagonal (Pi.single k c)).submatrix f f =
      A.submatrix f f + Matrix.diagonal (fun a => (Pi.single k c : ι → ℝ) (f a)) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.diagonal_apply, hf.eq_iff]
  rw [hsub]
  by_cases hk : ∃ k', f k' = k
  · obtain ⟨k', rfl⟩ := hk
    have : (fun a => (Pi.single (f k') c : ι → ℝ) (f a)) = Pi.single k' c := by
      funext a
      by_cases ha : a = k'
      · subst ha; simp
      · simp [Pi.single_apply, hf.ne ha, ha]
    rw [this, g_det_update, Matrix.submatrix_submatrix]
    have h1 := hA κ f hf
    have h2 := hA {j // j ≠ k'} (f ∘ fun j => (j : κ)) (hf.comp Subtype.val_injective)
    positivity
  · push_neg at hk
    have : (fun a => (Pi.single k c : ι → ℝ) (f a)) = 0 := by
      funext a; simp [Pi.single_apply, hk a]
    rw [this]
    simpa using hA κ f hf

lemma g_P_diag {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : g_P A) (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) : g_P (A + Matrix.diagonal d) := by
  classical
  have key : ∀ S : Finset ι, g_P (A + Matrix.diagonal (fun i => if i ∈ S then d i else 0)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hA
    | insert k S hk ih =>
      have : (fun i => if i ∈ insert k S then d i else 0) =
          fun i => (if i ∈ S then d i else 0) + (Pi.single k (d k) : ι → ℝ) i := by
        funext i
        by_cases hi : i = k
        · subst hi; simp [hk]
        · simp [hi, Pi.single_apply]
      rw [this, ← Matrix.diagonal_add, ← add_assoc]
      exact g_P_update _ ih k _ (hd k)
  simpa using key Finset.univ

lemma g_P_sub {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι ι ℝ) (hA : g_P A)
    (f : κ → ι) (hf : Function.Injective f) : g_P (A.submatrix f f) := by
  intro κ' _ _ g hg
  rw [Matrix.submatrix_submatrix]
  exact hA _ (f ∘ g) (hf.comp hg)

lemma g_P_of_IsP {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : IsPMatrix A) :
    g_P A := by
  intro κ _ _ f hf
  by_cases hκ : IsEmpty κ
  · rw [Matrix.det_isEmpty]; exact one_pos
  · rw [not_isEmpty_iff] at hκ
    obtain ⟨a0⟩ := hκ
    set J : Finset ι := Finset.univ.map ⟨f, hf⟩
    have hmem : ∀ a, f a ∈ J := fun a => Finset.mem_map_of_mem _ (Finset.mem_univ a)
    let e : κ ≃ J := Equiv.ofBijective (fun a => ⟨f a, hmem a⟩) ⟨fun a b h => hf (by simpa using h),
      fun ⟨j, hj⟩ => by
        obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hj
        exact ⟨a, rfl⟩⟩
    have : A.submatrix f f = (A.submatrix (fun i : J => (i : ι)) (fun i : J => (i : ι))).submatrix e e := by
      ext a b; rfl
    rw [this, Matrix.det_submatrix_equiv_self]
    exact hA J ⟨f a0, hmem a0⟩

lemma g_NSR_of_P {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : g_P A) : g_NSR A := by
  intro x hx
  by_contra hcon
  push_neg at hcon
  let κ := {i // x i ≠ 0}
  let f : κ → ι := fun j => j
  have hf : Function.Injective f := Subtype.val_injective
  let d : κ → ℝ := fun j => -(A *ᵥ x) j / x j
  have hd : ∀ j, 0 ≤ d j := by
    intro j
    have h1 := hcon j
    have h2 : x j ≠ 0 := j.2
    have : d j = -(x j * (A *ᵥ x) j) / (x j) ^ 2 := by
      simp only [d]; field_simp
    rw [this]; apply div_nonneg _ (sq_nonneg _); linarith
  have hP := g_P_diag _ (g_P_sub A hA f hf) d hd
  have hdet := hP κ id Function.injective_id
  rw [Matrix.submatrix_id_id] at hdet
  have hsum : ∀ j : κ, (A.submatrix f f *ᵥ (fun i => x i)) j = (A *ᵥ x) j := by
    intro j
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    have := Fintype.sum_subtype_add_sum_subtype (fun i => x i ≠ 0) (fun i => A j i * x i)
    rw [← this]
    have h0 : ∑ i : {i // ¬ x i ≠ 0}, A j i * x i = 0 := by
      apply Finset.sum_eq_zero; intro i _
      have : x i = 0 := by simpa using i.2
      simp [this]
    rw [h0, add_zero]
  have hzero : (A.submatrix f f + Matrix.diagonal d) *ᵥ (fun i => x i) = 0 := by
    funext j
    rw [Matrix.add_mulVec, Pi.add_apply, hsum, Matrix.mulVec_diagonal]
    have h2 : x j ≠ 0 := j.2
    simp only [d, Pi.zero_apply]
    field_simp
    ring
  have hne : (fun i : κ => x i) ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact hi (by simpa using congrFun h ⟨i, hi⟩)
  have : (A.submatrix f f + Matrix.diagonal d).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hzero⟩
  linarith


def g_hom {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  t • M + (1 - t) • (1 : Matrix ι ι ℝ)

lemma g_hom_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (t : ℝ) (v : ι → ℝ) (i : ι) :
    (g_hom M t *ᵥ v) i = t * (M *ᵥ v) i + (1 - t) * v i := by
  simp [g_hom, Matrix.add_mulVec, Matrix.smul_mulVec]

lemma g_NSR_hom {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : g_NSR (g_hom M t) := by
  intro x hx
  obtain ⟨i, hi⟩ := hM x hx
  refine ⟨i, ?_⟩
  rw [g_hom_mulVec]
  have hxi : x i ≠ 0 := by
    intro h; rw [h] at hi; simp at hi
  have : 0 < x i ^ 2 := by positivity
  rcases eq_or_lt_of_le ht0 with h | h
  · subst h; nlinarith
  · nlinarith

lemma g_NSR_det_ne {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) :
    M.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  obtain ⟨i, hi⟩ := hM v hv
  rw [hMv] at hi; simp at hi

lemma g_NSR_det_pos {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) :
    0 < M.det := by
  let f : ℝ → ℝ := fun t => (g_hom M t).det
  have hf : Continuous f := by
    have : Continuous fun t : ℝ => g_hom M t := by
      unfold g_hom; fun_prop
    exact this.matrix_det
  have h0 : f 0 = 1 := by simp [f, g_hom]
  have h1 : f 1 = M.det := by simp [f, g_hom]
  by_contra hneg
  push_neg at hneg
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨by rw [h1]; exact hneg, by rw [h0]; exact zero_le_one⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' zero_le_one hf.continuousOn hmem
  exact g_NSR_det_ne _ (g_NSR_hom M hM t ht.1 ht.2) hft

lemma g_NSR_subfin {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M)
    (J : Finset ι) : g_NSR (M.submatrix (fun i : J => (i : ι)) (fun i : J => (i : ι))) := by
  intro x hx
  let y : ι → ℝ := fun i => if h : i ∈ J then x ⟨i, h⟩ else 0
  have hy : y ≠ 0 := by
    intro h
    apply hx; funext j
    have := congrFun h j
    simpa [y, j.2] using this
  obtain ⟨i, hi⟩ := hM y hy
  have hiJ : i ∈ J := by
    by_contra h; simp [y, h] at hi
  refine ⟨⟨i, hiJ⟩, ?_⟩
  have hsum : (M *ᵥ y) i = (M.submatrix (fun i : J => (i : ι)) (fun i : J => (i : ι)) *ᵥ x) ⟨i, hiJ⟩ := by
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    rw [← Finset.sum_subset (Finset.subset_univ J)]
    · rw [← Finset.sum_coe_sort J]
      apply Finset.sum_congr rfl
      intro j _
      simp [y, j.2]
    · intro j _ hj
      simp [y, hj]
  have : y i = x ⟨i, hiJ⟩ := by simp [y, hiJ]
  rw [← this, ← hsum]; exact hi

lemma g_IsP_of_NSR {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) :
    IsPMatrix M := fun J _ => g_NSR_det_pos _ (g_NSR_subfin M hM J)


def g_Sol {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (q w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ (∀ i, 0 ≤ (M *ᵥ w + q) i) ∧ (∀ i, w i * (M *ᵥ w + q) i = 0)

lemma g_dchoice (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = 0)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hab' : a' * b' = 0) :
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧ (1 - d) * (a - a') + d * (b - b') = 0 := by
  set α := a - a'
  set β := b - b'
  have hαβ : α * β ≤ 0 := by
    have : α * β = a * b - a * b' - a' * b + a' * b' := by ring
    rw [this, hab, hab']; nlinarith [mul_nonneg ha hb', mul_nonneg ha' hb]
  by_cases h : α - β = 0
  · have hα : α = β := by linarith
    have : α = 0 := by rw [← hα] at hαβ; nlinarith [sq_nonneg α]
    exact ⟨0, le_rfl, zero_le_one, by rw [this]; ring⟩
  · refine ⟨α / (α - β), ?_, ?_, ?_⟩
    · have : α / (α - β) = α * (α - β) / (α - β) ^ 2 := by field_simp
      rw [this]; apply div_nonneg _ (sq_nonneg _); nlinarith [sq_nonneg α]
    · have : 1 - α / (α - β) = -β * (α - β) / (α - β) ^ 2 := by field_simp; ring
      have h2 : 0 ≤ -β * (α - β) / (α - β) ^ 2 := by
        apply div_nonneg _ (sq_nonneg _); nlinarith [sq_nonneg β]
      linarith
    · field_simp; ring

lemma g_lcp_bound {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) :
    ∃ c > 0, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ q q' w w' : ι → ℝ,
      g_Sol (g_hom M t) q w → g_Sol (g_hom M t) q' w' → c * ‖w - w'‖ ≤ ‖q - q'‖ := by
  let S : Set (ℝ × (ι → ℝ) × (ι → ℝ)) :=
    Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ι → ℝ) 1 ×ˢ Metric.sphere (0 : ι → ℝ) 1)
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod (isCompact_sphere _ _))
  let g : ℝ × (ι → ℝ) × (ι → ℝ) → ℝ := fun p =>
    ‖fun i => (1 - p.2.1 i) * p.2.2 i + p.2.1 i * (p.1 * (M *ᵥ p.2.2) i + (1 - p.1) * p.2.2 i)‖
  have hMc : Continuous fun x : ι → ℝ => M *ᵥ x :=
    (Matrix.mulVecLin M).continuous_of_finiteDimensional
  have hg : Continuous g := by
    have hc : ∀ i : ι, Continuous fun x : ι → ℝ => (M *ᵥ x) i := fun i =>
      (continuous_apply i).comp hMc
    apply continuous_norm.comp
    apply continuous_pi
    intro i
    have h1 : Continuous fun p : ℝ × (ι → ℝ) × (ι → ℝ) => (M *ᵥ p.2.2) i :=
      (hc i).comp (continuous_snd.comp continuous_snd)
    have h2 : Continuous fun p : ℝ × (ι → ℝ) × (ι → ℝ) => p.2.1 i :=
      (continuous_apply i).comp (continuous_fst.comp continuous_snd)
    have h3 : Continuous fun p : ℝ × (ι → ℝ) × (ι → ℝ) => p.2.2 i :=
      (continuous_apply i).comp (continuous_snd.comp continuous_snd)
    have h4 : Continuous fun p : ℝ × (ι → ℝ) × (ι → ℝ) => p.1 := continuous_fst
    fun_prop
  have hpos : ∀ p ∈ S, 0 < g p := by
    rintro ⟨t, d, x⟩ ⟨ht, hd, hx⟩
    simp only [Metric.mem_sphere, dist_zero_right] at hx
    have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; exact zero_ne_one hx
    apply lt_of_le_of_ne (norm_nonneg _)
    intro h0
    have hz := norm_eq_zero.mp h0.symm
    obtain ⟨i, hi⟩ := g_NSR_hom M hM t ht.1 ht.2 x hx0
    rw [g_hom_mulVec] at hi
    have e := congrFun hz i
    simp only [Pi.zero_apply] at e
    have hdi0 : 0 ≤ d i := hd.1 i
    have hdi1 : d i ≤ 1 := hd.2 i
    set m := t * (M *ᵥ x) i + (1 - t) * x i
    -- (1 - d) x + d m = 0 ⇒ x m ≤ 0
    have : x i * m ≤ 0 := by
      rcases eq_or_lt_of_le hdi0 with h | h
      · rw [← h] at e; simp at e; rw [e]; simp
      · have hm : d i * (x i * m) = -(1 - d i) * x i ^ 2 := by
          have : d i * m = -((1 - d i) * x i) := by linarith
          calc d i * (x i * m) = x i * (d i * m) := by ring
            _ = _ := by rw [this]; ring
        have : d i * (x i * m) ≤ 0 := by rw [hm]; nlinarith [sq_nonneg (x i)]
        by_contra hc; push_neg at hc
        nlinarith
    linarith
  obtain ⟨c, hc, hcS⟩ : ∃ c > 0, ∀ p ∈ S, c ≤ g p := by
    by_cases hne : S.Nonempty
    · obtain ⟨p0, hp0, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
      exact ⟨g p0, hpos p0 hp0, fun p hp => hmin hp⟩
    · exact ⟨1, one_pos, fun p hp => absurd ⟨p, hp⟩ hne⟩
  refine ⟨c, hc, fun t ht0 ht1 q q' w w' hw hw' => ?_⟩
  by_cases hx : w - w' = 0
  · rw [hx, norm_zero, mul_zero]; exact norm_nonneg _
  have hxn : 0 < ‖w - w'‖ := norm_pos_iff.mpr hx
  have hd : ∀ i, ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧ (1 - d) * (w i - w' i) +
      d * ((g_hom M t *ᵥ w + q) i - (g_hom M t *ᵥ w' + q') i) = 0 := fun i =>
    g_dchoice _ _ _ _ (hw.1 i) (hw.2.1 i) (hw.2.2 i) (hw'.1 i) (hw'.2.1 i) (hw'.2.2 i)
  choose d hd0 hd1 hdeq using hd
  set u := ‖w - w'‖⁻¹ • (w - w')
  have hu : (t, d, u) ∈ S := by
    refine ⟨⟨ht0, ht1⟩, ⟨fun i => hd0 i, fun i => hd1 i⟩, ?_⟩
    simp [u, norm_smul, hxn.ne']
  have hle := hcS _ hu
  have hgu : g (t, d, u) ≤ ‖w - w'‖⁻¹ * ‖q - q'‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have e := hdeq i
    have hlin : (g_hom M t *ᵥ w + q) i - (g_hom M t *ᵥ w' + q') i =
        t * (M *ᵥ (w - w')) i + (1 - t) * (w - w') i + (q - q') i := by
      simp only [Pi.add_apply, Pi.sub_apply, g_hom_mulVec, Matrix.mulVec_sub]; ring
    rw [hlin] at e
    have hcomp : (1 - d i) * u i + d i * (t * (M *ᵥ u) i + (1 - t) * u i) =
        ‖w - w'‖⁻¹ * (-(d i * (q - q') i)) := by
      simp only [u, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have : (1 - d i) * (w - w') i + d i * (t * (M *ᵥ (w - w')) i + (1 - t) * (w - w') i) =
          -(d i * (q - q') i) := by simp only [Pi.sub_apply] at e ⊢; linear_combination e
      rw [← this]; ring
    show ‖(1 - d i) * u i + d i * (t * (M *ᵥ u) i + (1 - t) * u i)‖ ≤ _
    rw [hcomp, norm_mul, norm_neg, norm_mul, Real.norm_eq_abs (‖w - w'‖⁻¹),
      abs_of_pos (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : ‖d i‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hd0 i, hd1 i]
    calc ‖d i‖ * ‖(q - q') i‖ ≤ 1 * ‖q - q'‖ :=
          mul_le_mul this (norm_le_pi_norm _ i) (norm_nonneg _) zero_le_one
      _ = ‖q - q'‖ := one_mul _
  have := hle.trans hgu
  have h2 : c * ‖w - w'‖ ≤ ‖w - w'‖⁻¹ * ‖q - q'‖ * ‖w - w'‖ :=
    mul_le_mul_of_nonneg_right this (norm_nonneg _)
  rwa [mul_assoc, mul_comm ‖q - q'‖, ← mul_assoc, inv_mul_cancel₀ hxn.ne', one_mul] at h2


lemma g_lcp_exists {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M) :
    ∀ q : ι → ℝ, ∃ w, g_Sol M q w := by
  obtain ⟨c, hc, hb⟩ := g_lcp_bound M hM
  let T := LinearMap.toContinuousLinearMap (Matrix.mulVecLin (M - 1))
  have hT : ∀ v, ‖(M - 1) *ᵥ v‖ ≤ ‖T‖ * ‖v‖ := fun v => T.le_opNorm v
  set E := ‖T‖ + 1
  have hE : 0 < E := by positivity
  set δ := c / (2 * E)
  have hδ : 0 < δ := by positivity
  have key : ∀ k : ℕ, ∀ q, ∃ w, g_Sol (g_hom M (min (k * δ) 1)) q w := by
    intro k
    induction k with
    | zero =>
      intro q
      refine ⟨fun i => max (-q i) 0, ?_⟩
      have h1 : g_hom M (min ((0 : ℕ) * δ) 1) = 1 := by simp [g_hom]
      rw [h1]
      refine ⟨fun i => le_max_right _ _, fun i => ?_, fun i => ?_⟩
      · simp only [Matrix.one_mulVec, Pi.add_apply]
        rcases le_total 0 (q i) with h | h
        · rw [max_eq_right (by linarith)]; linarith
        · rw [max_eq_left (by linarith)]; linarith
      · simp only [Matrix.one_mulVec, Pi.add_apply]
        rcases le_total 0 (q i) with h | h
        · rw [max_eq_right (by linarith)]; ring
        · rw [max_eq_left (by linarith)]; ring
    | succ k ih =>
      intro q
      set t0 := min (k * δ) 1
      set t1 := min (((k + 1 : ℕ) : ℝ) * δ) 1
      have ht0 : 0 ≤ t0 := le_min (by positivity) zero_le_one
      have ht0' : t0 ≤ 1 := min_le_right _ _
      have hdt0 : 0 ≤ t1 - t0 := by
        have : t0 ≤ t1 := min_le_min_right _ (by push_cast; nlinarith)
        linarith
      have hdt1 : t1 - t0 ≤ δ := by
        have : t1 ≤ t0 + δ := by
          rcases le_total (k * δ) 1 with h | h
          · have : t0 = k * δ := min_eq_left h
            rw [this]; exact (min_le_left _ _).trans (by push_cast; linarith)
          · have : t0 = 1 := min_eq_right h
            rw [this]; exact (min_le_right _ _).trans (by linarith)
        linarith
      choose S hS using ih
      let Φ : (ι → ℝ) → (ι → ℝ) := fun w => S (q + (t1 - t0) • ((M - 1) *ᵥ w))
      have hlip : LipschitzWith (1 / 2 : NNReal) Φ := by
        apply LipschitzWith.of_dist_le_mul
        intro w w'
        rw [dist_eq_norm, dist_eq_norm]
        have h := hb t0 ht0 ht0' _ _ _ _ (hS (q + (t1 - t0) • ((M - 1) *ᵥ w)))
          (hS (q + (t1 - t0) • ((M - 1) *ᵥ w')))
        have he : q + (t1 - t0) • ((M - 1) *ᵥ w) - (q + (t1 - t0) • ((M - 1) *ᵥ w')) =
            (t1 - t0) • ((M - 1) *ᵥ (w - w')) := by
          rw [Matrix.mulVec_sub, smul_sub]; abel
        rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hdt0] at h
        have h2 := hT (w - w')
        have h3 : (t1 - t0) * ‖(M - 1) *ᵥ (w - w')‖ ≤ δ * (E * ‖w - w'‖) := by
          apply mul_le_mul hdt1 (h2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)))
            (norm_nonneg _) hδ.le
        have h4 : δ * (E * ‖w - w'‖) = c / 2 * ‖w - w'‖ := by
          simp only [δ]; field_simp
        have : c * ‖Φ w - Φ w'‖ ≤ c * (1 / 2 * ‖w - w'‖) := by
          simp only [Φ]; nlinarith
        have := le_of_mul_le_mul_left this hc
        simpa using this
      have hcon : ContractingWith (1 / 2 : NNReal) Φ := ⟨by
        rw [← NNReal.coe_lt_coe]; norm_num, hlip⟩
      set w := ContractingWith.fixedPoint Φ hcon
      have hw : Φ w = w := ContractingWith.fixedPoint_isFixedPt hcon
      refine ⟨w, ?_⟩
      have hsol := hS (q + (t1 - t0) • ((M - 1) *ᵥ w))
      change g_Sol _ _ (Φ w) at hsol
      rw [hw] at hsol
      have heq : g_hom M t0 *ᵥ w + (q + (t1 - t0) • ((M - 1) *ᵥ w)) = g_hom M t1 *ᵥ w + q := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, g_hom_mulVec, Matrix.sub_mulVec,
          Matrix.one_mulVec, Pi.sub_apply]
        ring
      rw [g_Sol, heq] at hsol
      exact hsol
  intro q
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / δ)
  have hk1 : 1 ≤ k * δ := by
    have := mul_le_mul_of_nonneg_right hk hδ.le
    rwa [div_mul_cancel₀ _ hδ.ne'] at this
  obtain ⟨w, hw⟩ := key k q
  rw [min_eq_right hk1] at hw
  refine ⟨w, ?_⟩
  have : g_hom M 1 = M := by simp [g_hom]
  rwa [this] at hw


lemma g_hom_one {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : g_hom M 1 = M := by
  simp [g_hom]

lemma g_lcp_unique {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : g_NSR M)
    (q w w' : ι → ℝ) (hw : g_Sol M q w) (hw' : g_Sol M q w') : w = w' := by
  obtain ⟨c, hc, hb⟩ := g_lcp_bound M hM
  rw [← g_hom_one M] at hw hw'
  have := hb 1 zero_le_one le_rfl q q w w' hw hw'
  rw [sub_self, norm_zero] at this
  have h0 : ‖w - w'‖ = 0 := by nlinarith [norm_nonneg (w - w')]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

lemma g_NSR_of_unique {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (h : ∀ q w w', g_Sol M q w → g_Sol M q w' → w = w') : g_NSR M := by
  intro x hx
  by_contra hcon
  push_neg at hcon
  let a : ι → ℝ := fun i => max (x i) 0
  let b : ι → ℝ := fun i => max (-x i) 0
  let p : ι → ℝ := fun i => max ((M *ᵥ x) i) 0
  have hx_ab : x = a - b := by
    funext i; simp only [a, b, Pi.sub_apply]
    rcases le_total 0 (x i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hMab : M *ᵥ a - M *ᵥ b = M *ᵥ x := by rw [← Matrix.mulVec_sub, ← hx_ab]
  have ha : g_Sol M (p - M *ᵥ a) a := by
    have e : M *ᵥ a + (p - M *ᵥ a) = p := by abel
    refine ⟨fun i => le_max_right _ _, fun i => ?_, fun i => ?_⟩
    · rw [e]; exact le_max_right _ _
    · rw [e]; simp only [a, p]
      rcases le_total (x i) 0 with h1 | h1
      · rw [max_eq_right h1]; ring
      · rcases eq_or_lt_of_le h1 with h2 | h2
        · rw [← h2]; simp
        · have : (M *ᵥ x) i ≤ 0 := by
            by_contra h3; push_neg at h3; nlinarith [hcon i]
          rw [max_eq_right this]; ring
  have hb : g_Sol M (p - M *ᵥ a) b := by
    have e : M *ᵥ b + (p - M *ᵥ a) = fun i => max (-(M *ᵥ x) i) 0 := by
      funext i
      have hi : (M *ᵥ x) i = (M *ᵥ a) i - (M *ᵥ b) i := by rw [← hMab]; rfl
      simp only [p, Pi.add_apply, Pi.sub_apply]
      rcases le_total 0 ((M *ᵥ x) i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; linarith
      · rw [max_eq_right h, max_eq_left (by linarith)]; linarith
    refine ⟨fun i => le_max_right _ _, fun i => ?_, fun i => ?_⟩
    · rw [e]; exact le_max_right _ _
    · rw [e]; simp only [b]
      rcases le_total 0 (x i) with h1 | h1
      · rw [max_eq_right (by linarith)]; ring
      · rcases eq_or_lt_of_le h1 with h2 | h2
        · rw [h2]; simp
        · have : 0 ≤ (M *ᵥ x) i := by
            by_contra h3; push_neg at h3; nlinarith [hcon i]
          rw [max_eq_right (by linarith : -(M *ᵥ x) i ≤ 0)]; ring
  have := h _ _ _ ha hb
  apply hx
  rw [hx_ab, this, sub_self]

lemma g_lcp_iff {ι : Type} [Fintype ι] (M : Matrix ι ι ℝ) (z w : ι → ℝ) :
    ((∀ j, 0 ≤ (M *ᵥ w - z) j) ∧ (∀ j, 0 ≤ w j) ∧ w ⬝ᵥ (M *ᵥ w - z) = 0) ↔ g_Sol M (-z) w := by
  have e : M *ᵥ w + -z = M *ᵥ w - z := (sub_eq_add_neg _ _).symm
  unfold g_Sol
  rw [e]
  have hdot : ∀ (h1 : ∀ j, 0 ≤ (M *ᵥ w - z) j) (h2 : ∀ j, 0 ≤ w j),
      w ⬝ᵥ (M *ᵥ w - z) = 0 ↔ ∀ j, w j * (M *ᵥ w - z) j = 0 := by
    intro h1 h2
    unfold dotProduct
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (h2 j) (h1 j))]
    simp
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, (hdot h1 h2).mp h3⟩
  · rintro ⟨h2, h1, h3⟩
    exact ⟨h1, h2, (hdot h1 h2).mpr h3⟩

theorem lcp_core (s : ℕ) (M : Matrix (Fin s) (Fin s) ℝ) :
    (∀ z : Fin s → ℝ, ∃! w : Fin s → ℝ,
      (∀ j, 0 ≤ (M.mulVec w - z) j) ∧
      (∀ j, 0 ≤ w j) ∧
      w ⬝ᵥ (M.mulVec w - z) = 0) ↔ IsPMatrix M := by
  constructor
  · intro h
    apply g_IsP_of_NSR
    apply g_NSR_of_unique
    intro q w w' hw hw'
    obtain ⟨u, -, hu⟩ := h (-q)
    have e1 := hu w ((g_lcp_iff M (-q) w).mpr (by rwa [neg_neg]))
    have e2 := hu w' ((g_lcp_iff M (-q) w').mpr (by rwa [neg_neg]))
    rw [e1, e2]
  · intro hP z
    have hN := g_NSR_of_P M (g_P_of_IsP M hP)
    obtain ⟨w, hw⟩ := g_lcp_exists M hN (-z)
    refine ⟨w, (g_lcp_iff M z w).mpr hw, fun w' hw' => ?_⟩
    exact g_lcp_unique M hN (-z) w' w ((g_lcp_iff M z w').mp hw') hw


lemma g_nc_orth {s : ℕ} (v w : EuclideanSpace ℝ (Fin s)) :
    v ∈ normalCone (nonnegOrthant s) w ↔
      (∀ j, 0 ≤ w j) ∧ (∀ j, v j ≤ 0) ∧ ∀ j, w j * v j = 0 := by
  constructor
  · rintro ⟨hw, h⟩
    have hv : ∀ j, v j ≤ 0 := by
      intro j
      have := h (w + EuclideanSpace.single j 1) (by
        intro i
        have := hw i
        by_cases hij : i = j
        · subst hij; simp; linarith
        · simp [hij, this])
      simpa [EuclideanSpace.inner_single_right] using this
    refine ⟨hw, hv, fun j => ?_⟩
    have := h (w - EuclideanSpace.single j (w j)) (by
      intro i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, hw i])
    simp [EuclideanSpace.inner_single_right] at this
    have h1 := hw j
    have h2 := hv j
    nlinarith
  · rintro ⟨hw, hv, hwv⟩
    refine ⟨hw, fun c hc => ?_⟩
    rw [inner_sub_right]
    have h0 : ⟪v, w⟫ = 0 := by
      rw [PiLp.inner_apply]; apply Finset.sum_eq_zero; intro j _
      have := hwv j
      simp only [RCLike.inner_apply, conj_trivial]
      linarith [mul_comm (v j) (w j)]
    rw [h0, sub_zero, PiLp.inner_apply]
    apply Finset.sum_nonpos; intro j _
    have := hc j
    simp only [RCLike.inner_apply, conj_trivial]
    nlinarith [hv j]

lemma g_nc_sol {s : ℕ} (S : Matrix (Fin s) (Fin s) ℝ) (y w : EuclideanSpace ℝ (Fin s)) :
    y - S.toEuclideanLin w ∈ normalCone (nonnegOrthant s) w ↔ g_Sol S (-ofLp y) (ofLp w) := by
  rw [g_nc_orth]
  have e : ∀ j, (y - S.toEuclideanLin w) j = -((S *ᵥ ofLp w + -ofLp y) j) := by
    intro j; simp [g_tel]; ring
  simp only [e, g_Sol]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun j => by linarith [h2 j], fun j => by linarith [h3 j]⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun j => by linarith [h2 j], fun j => by linarith [h3 j]⟩

lemma g_Inv_of_P (s : ℕ) (S : Matrix (Fin s) (Fin s) ℝ) (hP : IsPMatrix S) :
    InvIsLipschitzFunction S (nonnegOrthant s) := by
  have hN := g_NSR_of_P S (g_P_of_IsP S hP)
  choose τ hτ using g_lcp_exists S hN
  obtain ⟨c, hc, hb⟩ := g_lcp_bound S hN
  let σ : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin s) := fun y => toLp 2 (τ (-ofLp y))
  let Φ := LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ (Fin s → ℝ)).symm.toLinearMap
  let Ψ := LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ (Fin s → ℝ)).toLinearMap
  have hΦ : ∀ v : Fin s → ℝ, ‖toLp 2 v‖ ≤ ‖Φ‖ * ‖v‖ := fun v => Φ.le_opNorm v
  have hΨ : ∀ v : EuclideanSpace ℝ (Fin s), ‖ofLp v‖ ≤ ‖Ψ‖ * ‖v‖ := fun v => Ψ.le_opNorm v
  refine ⟨‖Φ‖ * (1 / c) * ‖Ψ‖, σ, fun y => ⟨?_, fun w hw => ?_⟩, fun y1 y2 => ?_⟩
  · rw [g_nc_sol]; exact hτ _
  · rw [g_nc_sol] at hw
    have := g_lcp_unique S hN _ _ _ hw (hτ (-ofLp y))
    show w = toLp 2 (τ (-ofLp y))
    rw [← this]
  · have h1 := hb 1 zero_le_one le_rfl _ _ _ _ (by rw [g_hom_one]; exact hτ (-ofLp y1))
      (by rw [g_hom_one]; exact hτ (-ofLp y2))
    have e1 : -ofLp y1 - -ofLp y2 = -(ofLp (y1 - y2)) := by
      funext j; simp; ring
    rw [e1, norm_neg] at h1
    have h2 := hΨ (y1 - y2)
    have h3 : σ y1 - σ y2 = toLp 2 (τ (-ofLp y1) - τ (-ofLp y2)) := rfl
    rw [h3]
    refine (hΦ _).trans ?_
    have h4 : ‖τ (-ofLp y1) - τ (-ofLp y2)‖ ≤ (1 / c) * (‖Ψ‖ * ‖y1 - y2‖) := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]; linarith
    calc ‖Φ‖ * ‖τ (-ofLp y1) - τ (-ofLp y2)‖ ≤ ‖Φ‖ * ((1 / c) * (‖Ψ‖ * ‖y1 - y2‖)) :=
          mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = ‖Φ‖ * (1 / c) * ‖Ψ‖ * ‖y1 - y2‖ := by ring

theorem t31_core (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ) :
    (∀ K : Set (EuclideanSpace ℝ (Fin s)), K.Nonempty → IsClosed K → Convex ℝ K →
      A₁₁.det ≠ 0 → PosDefNS (schur A₁₁ A₁₂ A₂₁ A₂₂) →
      InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (prodSet K)) ∧
    (InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)
        (prodSet (nonnegOrthant s)) ↔
      A₁₁.det ≠ 0 ∧ IsPMatrix (schur A₁₁ A₁₂ A₂₁ A₂₂)) := by
  refine ⟨fun K hne hcl hcv hdet hPD =>
    block_core r s A₁₁ A₁₂ A₂₁ A₂₂ hdet K (smono_core s hs _ K hne hcl hcv hPD), ?_, ?_⟩
  · intro h
    have hdet := nonsingular_core r s A₁₁ A₁₂ A₂₁ A₂₂ h
    refine ⟨hdet, ?_⟩
    apply g_IsP_of_NSR
    apply g_NSR_of_unique
    intro q w w' hw hw'
    obtain ⟨L, σ, hσ, -⟩ := h
    let y : EuclideanSpace ℝ (Fin r ⊕ Fin s) := g_join 0 (toLp 2 (-q))
    have key : ∀ u, g_Sol (schur A₁₁ A₁₂ A₂₁ A₂₂) q u →
        g_join ((A₁₁⁻¹).toEuclideanLin (upperBlock y) -
          (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (toLp 2 u))) (toLp 2 u) = σ y := by
      intro u hu
      apply (hσ y).2
      rw [inclusion_core r s A₁₁ A₁₂ A₂₁ A₂₂ hdet, g_upper_join, g_lower_join]
      refine ⟨rfl, ?_⟩
      have e : lowerBlock y - A₂₁.toEuclideanLin ((A₁₁⁻¹).toEuclideanLin (upperBlock y)) = toLp 2 (-q) := by
        simp [y, g_upper_join, g_lower_join]
      rw [e, g_nc_sol]
      simpa using hu
    have := congrArg lowerBlock ((key w hw).trans (key w' hw').symm)
    rw [g_lower_join, g_lower_join] at this
    exact congrArg ofLp this
  · rintro ⟨hdet, hP⟩
    exact block_core r s A₁₁ A₁₂ A₂₁ A₂₂ hdet _ (g_Inv_of_P s _ hP)

end RobinsonSR.Schur

open RobinsonSR.Schur


theorem solution (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ) :
    (∀ K : Set (EuclideanSpace ℝ (Fin s)), K.Nonempty → IsClosed K → Convex ℝ K →
      A₁₁.det ≠ 0 → PosDefNS (schur A₁₁ A₁₂ A₂₁ A₂₂) →
      InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) (prodSet K)) ∧
    (InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)
        (prodSet (nonnegOrthant s)) ↔
      A₁₁.det ≠ 0 ∧ IsPMatrix (schur A₁₁ A₁₂ A₂₁ A₂₂)) := by
  exact t31_core r s hr hs A₁₁ A₁₂ A₂₁ A₂₂
