-- Prove2me | solution 1 for RobinsonSR.Schur.strongly_monotone_inverse_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:26:37.124559+00:00
-- url     : https://prove2.me/submissions/3e4f19a7-df83-4bbb-824a-290044bda854

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting



namespace RobinsonSR.Schur

open scoped RealInnerProductSpace Matrix
open WithLp

lemma g_tel {m n : Type*} [Fintype n] [DecidableEq n] (M : Matrix m n ℝ) (v : EuclideanSpace ℝ n) :
    M.toEuclideanLin v = toLp 2 (M *ᵥ ofLp v) := rfl

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

end RobinsonSR.Schur

open RobinsonSR.Schur


theorem solution (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (hA₁₁ : A₁₁.det ≠ 0)
    (K : Set (EuclideanSpace ℝ (Fin s)))
    (hK₁ : K.Nonempty) (hK₂ : IsClosed K) (hK₃ : Convex ℝ K)
    (hM : PosDefNS (schur A₁₁ A₁₂ A₂₁ A₂₂)) :
    InvIsLipschitzFunction (schur A₁₁ A₁₂ A₂₁ A₂₂) K := by
  exact smono_core s hs (schur A₁₁ A₁₂ A₂₁ A₂₂) K hK₁ hK₂ hK₃ hM
