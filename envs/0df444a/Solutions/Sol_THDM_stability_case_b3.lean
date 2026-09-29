-- Prove2me | solution 1 for THDM.stability_case_b3
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:10:51.821376+00:00
-- url     : https://prove2.me/submissions/98506abd-12f7-4937-9ada-0cb9793e81ae

import Definitions.Def_THDM_stationary

open scoped BigOperators
open Matrix
open THDM

theorem W3a_THDM_contJ4 (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) :
    Continuous (fun k => J4 eta00 eta E k) := by
  simp only [J4, dot3, quad3, Fin.sum_univ_three]
  fun_prop

theorem W3a_THDM_contJ2 (xi0 : ℝ) (xi : Fin 3 → ℝ) :
    Continuous (fun k => J2 xi0 xi k) := by
  simp only [J2, dot3, Fin.sum_univ_three]
  fun_prop

theorem W3a_THDM_zero_mem : (0 : Fin 3 → ℝ) ∈ ballK := by
  simp [ballK, dot3]

theorem W3a_THDM_ballK_compact : IsCompact ballK := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : Continuous (fun k : Fin 3 → ℝ => dot3 k k) := by
      simp only [dot3, Fin.sum_univ_three]
      fun_prop
    exact isClosed_le this continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun k hk => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro a
    rw [Real.norm_eq_abs, abs_le]
    have hk' : dot3 k k ≤ 1 := hk
    simp only [dot3, Fin.sum_univ_three] at hk'
    have h0 := mul_self_nonneg (k 0)
    have h1 := mul_self_nonneg (k 1)
    have h2 := mul_self_nonneg (k 2)
    fin_cases a <;> simp <;> constructor <;> nlinarith

theorem W3a_THDM_bound (m m2 k0 a b : ℝ) (hm : 0 < m) (hk0 : 0 ≤ k0) (ha : m2 ≤ a)
    (hb : m ≤ b) : -m2 ^ 2 / (4 * m) ≤ k0 * a + k0 ^ 2 * b := by
  rw [div_le_iff₀ (by linarith)]
  have h1 := mul_le_mul_of_nonneg_left ha hk0
  have h2 := mul_le_mul_of_nonneg_left hb (sq_nonneg k0)
  nlinarith [sq_nonneg (2 * m * k0 + m2)]

theorem W3a_THDM_stability_case_a_and_b2
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) :
    ((∃ k ∈ ballK, J4 eta00 eta E k < 0) → ¬ Stable xi0 xi eta00 eta E) ∧
    (StrongStable eta00 eta E → Stable xi0 xi eta00 eta E) := by
  constructor
  · rintro ⟨k, hk, hneg⟩ ⟨C, hC⟩
    set a := -J4 eta00 eta E k with hadef
    set b := J2 xi0 xi k
    have ha : 0 < a := by linarith
    set t := max 1 ((|b| + |C| + 1) / a) with htdef
    have ht1 : 1 ≤ t := le_max_left _ _
    have ht2 : (|b| + |C| + 1) / a ≤ t := le_max_right _ _
    rw [div_le_iff₀ ha] at ht2
    have hV := hC t k hk (by linarith)
    simp only [Vpot] at hV
    have hJ4 : J4 eta00 eta E k = -a := by rw [hadef]; ring
    rw [hJ4] at hV
    have hb1 := le_abs_self b
    have hC1 := neg_abs_le C
    have key : t * b + t ^ 2 * -a ≤ -t * (|C| + 1) := by
      have : t * (a * t) ≥ t * (|b| + |C| + 1) := by nlinarith
      nlinarith
    nlinarith [abs_nonneg C]
  · intro hS
    obtain ⟨k1, hk1, hmin1⟩ := W3a_THDM_ballK_compact.exists_isMinOn ⟨0, W3a_THDM_zero_mem⟩
      (W3a_THDM_contJ4 eta00 eta E).continuousOn
    obtain ⟨k2, _, hmin2⟩ := W3a_THDM_ballK_compact.exists_isMinOn ⟨0, W3a_THDM_zero_mem⟩
      (W3a_THDM_contJ2 xi0 xi).continuousOn
    refine ⟨-(J2 xi0 xi k2) ^ 2 / (4 * J4 eta00 eta E k1), fun k0 k hk hk0 => ?_⟩
    simp only [Vpot]
    exact W3a_THDM_bound _ _ _ _ _ (hS k1 hk1) hk0 (isMinOn_iff.mp hmin2 k hk)
      (isMinOn_iff.mp hmin1 k hk)

theorem solution
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) :
    WeakStable xi0 xi eta00 eta E → Stable xi0 xi eta00 eta E := by
  intro hW
  have hJ4nn : ∀ k ∈ ballK, 0 ≤ J4 eta00 eta E k := fun k hk =>
    (hW k hk).elim le_of_lt (fun h => h.1.ge)
  obtain ⟨k2, _, hmin2⟩ := W3a_THDM_ballK_compact.exists_isMinOn ⟨0, W3a_THDM_zero_mem⟩
    (W3a_THDM_contJ2 xi0 xi).continuousOn
  have hSc : IsCompact (ballK ∩ {k | J2 xi0 xi k ≤ 0}) :=
    W3a_THDM_ballK_compact.inter_right (isClosed_le (W3a_THDM_contJ2 xi0 xi) continuous_const)
  by_cases hne : (ballK ∩ {k | J2 xi0 xi k ≤ 0}).Nonempty
  · obtain ⟨k1, hk1, hmin1⟩ := hSc.exists_isMinOn hne (W3a_THDM_contJ4 eta00 eta E).continuousOn
    have hpos : 0 < J4 eta00 eta E k1 := by
      rcases hW k1 hk1.1 with h | ⟨_, h2⟩
      · exact h
      · exact absurd hk1.2 (not_le.mpr h2)
    refine ⟨min 0 (-(J2 xi0 xi k2) ^ 2 / (4 * J4 eta00 eta E k1)), fun k0 k hk hk0 => ?_⟩
    simp only [Vpot]
    by_cases hJ2 : J2 xi0 xi k ≤ 0
    · exact (min_le_right _ _).trans (W3a_THDM_bound _ _ _ _ _ hpos hk0
        (isMinOn_iff.mp hmin2 k hk) (isMinOn_iff.mp hmin1 k ⟨hk, hJ2⟩))
    · push_neg at hJ2
      have := hJ4nn k hk
      refine (min_le_left _ _).trans ?_
      nlinarith [mul_nonneg hk0 hJ2.le, mul_nonneg (sq_nonneg k0) this]
  · refine ⟨0, fun k0 k hk hk0 => ?_⟩
    simp only [Vpot]
    have hJ2 : 0 < J2 xi0 xi k := by
      by_contra h
      exact hne ⟨k, hk, not_lt.mp h⟩
    have := hJ4nn k hk
    nlinarith [mul_nonneg hk0 hJ2.le, mul_nonneg (sq_nonneg k0) this]

theorem W3a_THDM_stability_case_b4_marginal
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hm : MarginalCase xi0 xi eta00 eta E) :
    Stable xi0 xi eta00 eta E ↔
      ∃ C : ℝ, 0 < C ∧ ∀ k ∈ B3region xi0 xi eta00 eta E,
        (J2 xi0 xi k) ^ 2 ≤ C * J4 eta00 eta E k := by
  constructor
  · rintro ⟨C0, hC0⟩
    have h00 := hC0 0 0 W3a_THDM_zero_mem le_rfl
    simp only [Vpot] at h00
    refine ⟨-4 * C0 + 1, by nlinarith, fun k hk => ?_⟩
    obtain ⟨hkb, hJ4, hJ2⟩ := hk
    set a := J2 xi0 xi k
    set b := J4 eta00 eta E k
    have hk0 : 0 ≤ -a / (2 * b) := div_nonneg (by linarith) (by linarith)
    have hV := hC0 (-a / (2 * b)) k hkb hk0
    simp only [Vpot] at hV
    have hb0 : b ≠ 0 := ne_of_gt hJ4
    have e : -a / (2 * b) * a + (-a / (2 * b)) ^ 2 * b = -a ^ 2 / (4 * b) := by
      field_simp
      ring
    rw [e, le_div_iff₀ (by linarith)] at hV
    nlinarith
  · rintro ⟨C, hC, h⟩
    refine ⟨-C / 4, fun k0 k hk hk0 => ?_⟩
    simp only [Vpot]
    rcases hm.1 k hk with hJ4 | ⟨hJ4, hJ2⟩
    · by_cases hJ2 : J2 xi0 xi k < 0
      · have hB := h k ⟨hk, hJ4, hJ2⟩
        have key : -C * J4 eta00 eta E k ≤
            4 * J4 eta00 eta E k * (k0 * J2 xi0 xi k + k0 ^ 2 * J4 eta00 eta E k) := by
          nlinarith [sq_nonneg (2 * J4 eta00 eta E k * k0 + J2 xi0 xi k)]
        by_contra hcon
        push_neg at hcon
        nlinarith
      · push_neg at hJ2
        nlinarith [mul_nonneg hk0 hJ2, mul_nonneg (sq_nonneg k0) hJ4.le]
    · rw [hJ4]
      nlinarith [mul_nonneg hk0 hJ2]

/-! ### Theorem 2: stationary points -/

theorem W3a_THDM_dot4 (x y : Idx → ℝ) : dot4 x y = x ⬝ᵥ y := rfl

theorem W3a_THDM_ET_symm (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (hE : E.IsSymm) : (ET eta00 eta E)ᵀ = ET eta00 eta E := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.transpose_apply, ET, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
  exact hE.apply i j

theorem W3a_THDM_gT_symm : gTᵀ = gT := by
  simp [gT, Matrix.fromBlocks_transpose]

theorem W3a_THDM_M_symm (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ)
    (hE : E.IsSymm) (u : ℝ) :
    (ET eta00 eta E - u • gT)ᵀ = ET eta00 eta E - u • gT := by
  rw [Matrix.transpose_sub, Matrix.transpose_smul, W3a_THDM_ET_symm eta00 eta E hE,
    W3a_THDM_gT_symm]

theorem W3a_THDM_mink_KT (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) (u : ℝ) :
    mink (KT xi0 xi eta00 eta E u) = -fTPrime xi0 xi eta00 eta E u := by
  have hN : ((ET eta00 eta E - u • gT)⁻¹)ᵀ = (ET eta00 eta E - u • gT)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, W3a_THDM_M_symm eta00 eta E hE u]
  simp only [mink, KT, fTPrime, W3a_THDM_dot4]
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (xiT xi0 xi), ← Matrix.mulVec_transpose, hN]
  simp only [smul_eq_mul]
  ring

theorem W3a_THDM_KT_solves (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) (h : RegT eta00 eta E u) :
    (ET eta00 eta E - u • gT) *ᵥ KT xi0 xi eta00 eta E u = (-(1 / 2 : ℝ)) • xiT xi0 xi := by
  rw [KT, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h,
    Matrix.one_mulVec]

theorem W3a_THDM_eq_KT (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) (h : RegT eta00 eta E u) (x : Idx → ℝ)
    (hx : (ET eta00 eta E - u • gT) *ᵥ x = (-(1 / 2 : ℝ)) • xiT xi0 xi) :
    x = KT xi0 xi eta00 eta E u := by
  rw [KT, ← Matrix.mulVec_smul, ← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h,
    Matrix.one_mulVec]

theorem W3a_THDM_thm2_stationary_points
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) (x : Idx → ℝ) :
    IsStatPoint xi0 xi eta00 eta E x ↔
      (-- (I a)
        (RegT eta00 eta E 0 ∧ fTPrime xi0 xi eta00 eta E 0 < 0 ∧
          0 < comp0 (KT xi0 xi eta00 eta E 0) ∧ x = KT xi0 xi eta00 eta E 0) ∨
      -- (I b)
        (¬ RegT eta00 eta E 0 ∧ 0 < comp0 x ∧ 0 < mink x ∧
          ET eta00 eta E *ᵥ x = (-(1 / 2 : ℝ)) • xiT xi0 xi) ∨
      -- (II a)
        (∃ u : ℝ, RegT eta00 eta E u ∧ fTPrime xi0 xi eta00 eta E u = 0 ∧
          0 < comp0 (KT xi0 xi eta00 eta E u) ∧ x = KT xi0 xi eta00 eta E u) ∨
      -- (II b)
        (∃ u : ℝ, ¬ RegT eta00 eta E u ∧ 0 < comp0 x ∧ mink x = 0 ∧
          (ET eta00 eta E - u • gT) *ᵥ x = (-(1 / 2 : ℝ)) • xiT xi0 xi) ∨
      -- (III)
        x = 0) := by
  have h0 : ET eta00 eta E - (0 : ℝ) • gT = ET eta00 eta E := by simp
  constructor
  · rintro (hx | ⟨hc, hm, heq⟩ | ⟨hc, hm, u, heq⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr hx)))
    · by_cases hR : RegT eta00 eta E 0
      · have hxK : x = KT xi0 xi eta00 eta E 0 :=
          W3a_THDM_eq_KT xi0 xi eta00 eta E 0 hR x (by rw [h0]; exact heq)
        have hmk := W3a_THDM_mink_KT xi0 xi eta00 eta E hE 0
        rw [← hxK] at hmk
        refine Or.inl ⟨hR, by linarith, by rw [← hxK]; exact hc, hxK⟩
      · exact Or.inr (Or.inl ⟨hR, hc, hm, heq⟩)
    · by_cases hR : RegT eta00 eta E u
      · have hxK : x = KT xi0 xi eta00 eta E u := W3a_THDM_eq_KT xi0 xi eta00 eta E u hR x heq
        have hmk := W3a_THDM_mink_KT xi0 xi eta00 eta E hE u
        rw [← hxK] at hmk
        exact Or.inr (Or.inr (Or.inl ⟨u, hR, by linarith, by rw [← hxK]; exact hc, hxK⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u, hR, hc, hm, heq⟩)))
  · rintro (⟨hR, hf, hc, hx⟩ | ⟨_, hc, hm, heq⟩ | ⟨u, hR, hf, hc, hx⟩ | ⟨u, _, hc, hm, heq⟩ | hx)
    · have hmk := W3a_THDM_mink_KT xi0 xi eta00 eta E hE 0
      have hs := W3a_THDM_KT_solves xi0 xi eta00 eta E 0 hR
      rw [h0] at hs
      subst hx
      exact Or.inr (Or.inl ⟨hc, by linarith, hs⟩)
    · exact Or.inr (Or.inl ⟨hc, hm, heq⟩)
    · have hmk := W3a_THDM_mink_KT xi0 xi eta00 eta E hE u
      have hs := W3a_THDM_KT_solves xi0 xi eta00 eta E u hR
      subst hx
      exact Or.inr (Or.inr ⟨hc, by linarith, u, hs⟩)
    · exact Or.inr (Or.inr ⟨hc, hm, u, heq⟩)
    · exact Or.inl hx
