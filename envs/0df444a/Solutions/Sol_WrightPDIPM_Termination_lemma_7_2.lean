-- Prove2me | solution 1 for WrightPDIPM.Termination.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T19:45:10.141141+00:00
-- url     : https://prove2.me/submissions/1bd81368-cc22-4c85-8ddb-30d121a0d9cc

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

open WrightPDIPM.Termination
open Matrix

/-- property: no nonzero kernel vector conformal to `w` -/
def g72wyb_NoConf {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) (w : Fin q → ℝ) : Prop :=
  ∀ z : Fin q → ℝ, H *ᵥ z = 0 → (∀ j, z j ≠ 0 → 0 < z j * w j) → z = 0

lemma g72wyb_sq_sign (t : SignType) : ((t : ℝ)) ^ 2 = if t = 0 then 0 else 1 := by
  cases t <;> simp

lemma g72wyb_pat {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) (τ : Fin q → SignType) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Fin q → ℝ, (∀ j, SignType.sign (w j) = τ j) →
      g72wyb_NoConf H w → ‖w‖ ≤ C * ‖H *ᵥ w‖ := by
  set T : Set (Fin q → ℝ) := (⋂ j, {u : Fin q → ℝ | 0 ≤ (τ j : ℝ) * u j} ∩
      {u | u j = (τ j : ℝ) ^ 2 * u j}) ∩ Metric.sphere 0 1 with hT
  have hTc : IsCompact T := by
    apply (isCompact_sphere (0 : Fin q → ℝ) 1).inter_left
    apply isClosed_iInter
    intro j
    apply IsClosed.inter
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  -- members of T are conformal to w of pattern τ
  have hconf : ∀ u ∈ T, ∀ w : Fin q → ℝ, (∀ j, SignType.sign (w j) = τ j) →
      ∀ j, u j ≠ 0 → 0 < u j * w j := by
    intro u hu w hw j hj
    have hu1 := (Set.mem_iInter.mp hu.1 j).1
    have hu2 := (Set.mem_iInter.mp hu.1 j).2
    simp only [Set.mem_setOf_eq] at hu1 hu2
    have hwj := hw j
    rcases lt_trichotomy (w j) 0 with h | h | h
    · rw [sign_neg h] at hwj
      rw [← hwj] at hu1
      simp at hu1
      have : u j < 0 := lt_of_le_of_ne (by linarith) hj
      nlinarith
    · rw [h, sign_zero] at hwj
      rw [← hwj] at hu2
      simp at hu2
      exact absurd hu2 hj
    · rw [sign_pos h] at hwj
      rw [← hwj] at hu1
      simp at hu1
      have : 0 < u j := lt_of_le_of_ne hu1 (Ne.symm hj)
      nlinarith
  have hmemT : ∀ w : Fin q → ℝ, (∀ j, SignType.sign (w j) = τ j) → w ≠ 0 →
      ‖w‖⁻¹ • w ∈ T := by
    intro w hw hw0
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    refine ⟨Set.mem_iInter.mpr fun j => ⟨?_, ?_⟩, ?_⟩
    · simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
      rw [← hw j]
      rcases lt_trichotomy (w j) 0 with h | h | h
      · rw [sign_neg h]; simp; have := inv_pos.mpr hn; nlinarith
      · rw [h]; simp
      · rw [sign_pos h]; simp; positivity
    · simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
      rw [← hw j]
      rcases lt_trichotomy (w j) 0 with h | h | h
      · rw [sign_neg h]; simp
      · rw [h]; simp
      · rw [sign_pos h]; simp
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  by_cases hbad : ∃ u ∈ T, H *ᵥ u = 0
  · obtain ⟨u, hu, hHu⟩ := hbad
    refine ⟨0, le_rfl, fun w hw hnc => ?_⟩
    exfalso
    have h0 := hnc u hHu (hconf u hu w hw)
    have := hu.2
    rw [h0, mem_sphere_zero_iff_norm, norm_zero] at this
    exact zero_ne_one this
  push_neg at hbad
  rcases T.eq_empty_or_nonempty with hE | hNE
  · refine ⟨0, le_rfl, fun w hw _ => ?_⟩
    by_cases hw0 : w = 0
    · simp [hw0]
    · have := hmemT w hw hw0
      rw [hE] at this
      exact absurd this (Set.notMem_empty _)
  · obtain ⟨u0, hu0, hmin⟩ := hTc.exists_isMinOn hNE
      (f := fun u => ‖H *ᵥ u‖) (by fun_prop)
    have hc : 0 < ‖H *ᵥ u0‖ := norm_pos_iff.mpr (hbad u0 hu0)
    refine ⟨‖H *ᵥ u0‖⁻¹, by positivity, fun w hw _ => ?_⟩
    by_cases hw0 : w = 0
    · simp [hw0]
    · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have h1 := hmin (hmemT w hw hw0)
      simp only [Set.mem_setOf_eq, Matrix.mulVec_smul, norm_smul, norm_inv, norm_norm] at h1
      rw [le_inv_mul_iff₀ hc]
      have h2 : ‖H *ᵥ u0‖ * ‖w‖ ≤ ‖w‖⁻¹ * ‖H *ᵥ w‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right h1 hn.le
      have e : ‖w‖⁻¹ * ‖H *ᵥ w‖ * ‖w‖ = ‖H *ᵥ w‖ := by field_simp
      rw [e] at h2
      linarith

lemma g72wyb_core {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Fin q → ℝ, g72wyb_NoConf H w → ‖w‖ ≤ C * ‖H *ᵥ w‖ := by
  choose C hC0 hC using g72wyb_pat H
  refine ⟨∑ τ, C τ, Finset.sum_nonneg fun τ _ => hC0 τ, fun w hw => ?_⟩
  have h1 := hC (fun j => SignType.sign (w j)) w (fun j => rfl) hw
  have h2 : C (fun j => SignType.sign (w j)) ≤ ∑ τ, C τ :=
    Finset.single_le_sum (fun τ _ => hC0 τ) (Finset.mem_univ _)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- Euclidean norm comparisons. -/
lemma g72wyb_sup_le_e {q : ℕ} (v : Fin q → ℝ) : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => v i ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ i))

lemma g72wyb_e_le_sup {q : ℕ} (v : Fin q → ℝ) :
    Real.sqrt (∑ i, v i ^ 2) ≤ Real.sqrt q * ‖v‖ := by
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (Nat.cast_nonneg q)]
  apply Real.sqrt_le_sqrt
  have : ∀ i, v i ^ 2 ≤ ‖v‖ ^ 2 := fun i => by
    rw [← sq_abs]
    have := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at this
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin q, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => this i
    _ = q * ‖v‖ ^ 2 := by simp

lemma g72wyb_core2 {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Fin q → ℝ, g72wyb_NoConf H w →
      Real.sqrt (∑ i, w i ^ 2) ≤ C * Real.sqrt (∑ i, (H *ᵥ w) i ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := g72wyb_core H
  refine ⟨Real.sqrt q * C, by positivity, fun w hw => ?_⟩
  calc Real.sqrt (∑ i, w i ^ 2) ≤ Real.sqrt q * ‖w‖ := g72wyb_e_le_sup w
    _ ≤ Real.sqrt q * (C * ‖H *ᵥ w‖) := mul_le_mul_of_nonneg_left (hC w hw) (by positivity)
    _ ≤ Real.sqrt q * (C * Real.sqrt (∑ i, (H *ᵥ w) i ^ 2)) := by
        gcongr; exact g72wyb_sup_le_e _
    _ = _ := by ring

lemma g72wyb_expand {q : ℕ} (σ wb z : Fin q → ℝ) (t : ℝ) :
    ∑ j, (σ j * (wb j - t * z j)) ^ 2 = ∑ j, (σ j * wb j) ^ 2
      - 2 * t * ∑ j, σ j ^ 2 * (z j * wb j) + t ^ 2 * ∑ j, σ j ^ 2 * z j ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma g72wyb_wls_noconf {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) (σ : Fin q → ℝ)
    (hσ : ∀ j, σ j ≠ 0) (h : Fin p → ℝ) (wb : Fin q → ℝ) (hw : IsWLSSolution H σ h wb) :
    g72wyb_NoConf H wb := by
  intro z hz hconf
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  set a := ∑ j, σ j ^ 2 * (z j * wb j) with ha
  set b := ∑ j, σ j ^ 2 * z j ^ 2 with hb
  have hterm : ∀ i, 0 ≤ σ i ^ 2 * (z i * wb i) := by
    intro i
    by_cases hi : z i = 0
    · simp [hi]
    · exact mul_nonneg (sq_nonneg _) (hconf i hi).le
  have hσj : 0 < σ j ^ 2 := by have := hσ j; positivity
  have ha0 : 0 < a := Finset.sum_pos' (fun i _ => hterm i)
    ⟨j, Finset.mem_univ j, mul_pos hσj (hconf j hj)⟩
  have hb0 : 0 < b := Finset.sum_pos' (fun i _ => by positivity)
    ⟨j, Finset.mem_univ j, mul_pos hσj (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj)))⟩
  set t := a / b with ht
  have hfeas : H *ᵥ (wb - t • z) = h := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hz, smul_zero, sub_zero, hw.1]
  have hle := hw.2 _ hfeas
  have e : ∑ j, (σ j * (wb - t • z) j) ^ 2 = ∑ j, (σ j * (wb j - t * z j)) ^ 2 := by
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [e, g72wyb_expand] at hle
  have : t ^ 2 * b = t * a := by rw [ht]; field_simp
  nlinarith [mul_pos (div_pos ha0 hb0) ha0]

/-- Lemma 7.2 (p. 131): for `H ∈ ℝ^{p×q}` there is a constant `Ĉ ≥ 0` depending only on `H` such
that for every `h ∈ Range(H)` and every nonsingular diagonal `Σ = diag(σ)`, the problem (7.7)
`min_w ½‖Σw‖² s.t. Hw = h` has a unique solution `w̄`, and it satisfies `‖w̄‖ ≤ Ĉ‖h‖`. -/
theorem solution {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) :
    ∃ Chat : ℝ, 0 ≤ Chat ∧ ∀ h : Fin p → ℝ, (∃ w₀ : Fin q → ℝ, H *ᵥ w₀ = h) →
      ∀ σ : Fin q → ℝ, (∀ j, σ j ≠ 0) →
        (∃! wbar : Fin q → ℝ, IsWLSSolution H σ h wbar) ∧
        ∀ wbar : Fin q → ℝ, IsWLSSolution H σ h wbar → norm2 wbar ≤ Chat * norm2 h := by
  obtain ⟨C, hC0, hC⟩ := g72wyb_core2 H
  refine ⟨C, hC0, fun h ⟨w₀, hw₀⟩ σ hσ => ⟨?_, fun wb hwb => ?_⟩⟩
  · -- existence and uniqueness
    set obj : (Fin q → ℝ) → ℝ := fun w => ∑ j, (σ j * w j) ^ 2 with hobj
    set S : Set (Fin q → ℝ) := {w | H *ᵥ w = h} ∩ {w | obj w ≤ obj w₀} with hS
    have hSc : IsCompact S := by
      apply Metric.isCompact_of_isClosed_isBounded
      · apply IsClosed.inter
        · exact isClosed_eq (Continuous.matrix_mulVec continuous_const continuous_id)
            continuous_const
        · exact isClosed_le (by rw [hobj]; fun_prop) continuous_const
      · rw [Metric.isBounded_iff_subset_closedBall 0]
        refine ⟨∑ j, Real.sqrt (obj w₀) / |σ j|, fun w hw => ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => by positivity)).2
          fun i => ?_
        have hσi : 0 < |σ i| := abs_pos.mpr (hσ i)
        have h1 : (σ i * w i) ^ 2 ≤ obj w₀ := by
          refine le_trans ?_ hw.2
          exact Finset.single_le_sum (f := fun j => (σ j * w j) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        have h2 : |σ i| * |w i| ≤ Real.sqrt (obj w₀) := by
          rw [← abs_mul, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h1
        have h3 : |w i| ≤ Real.sqrt (obj w₀) / |σ i| := by
          rw [le_div_iff₀ hσi]; linarith
        rw [Real.norm_eq_abs]
        refine h3.trans ?_
        exact Finset.single_le_sum (f := fun j => Real.sqrt (obj w₀) / |σ j|)
          (fun j _ => by positivity) (Finset.mem_univ i)
    have hne : S.Nonempty := ⟨w₀, hw₀, show obj w₀ ≤ obj w₀ from le_rfl⟩
    obtain ⟨wb, hwbS, hmin⟩ := hSc.exists_isMinOn hne (f := obj) (by rw [hobj]; fun_prop)
    have hwls : IsWLSSolution H σ h wb := by
      refine ⟨hwbS.1, fun w hw => ?_⟩
      by_cases hlt : obj w ≤ obj w₀
      · exact hmin ⟨hw, hlt⟩
      · push_neg at hlt
        exact (hwbS.2.trans hlt.le)
    refine ⟨wb, hwls, fun w2 hw2 => ?_⟩
    -- uniqueness
    have hmid : H *ᵥ ((1/2 : ℝ) • (w2 + wb)) = h := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_add, hw2.1, hwls.1]
      ext i; simp; ring
    have h1 := hw2.2 _ hmid
    have h2 := hwls.2 _ hmid
    have e : ∑ j, (σ j * ((1/2 : ℝ) • (w2 + wb)) j) ^ 2 =
        (1/2) * ∑ j, (σ j * w2 j) ^ 2 + (1/2) * ∑ j, (σ j * wb j) ^ 2
          - (1/4) * ∑ j, (σ j * (w2 j - wb j)) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [e] at h1 h2
    have h3 : ∑ j, (σ j * (w2 j - wb j)) ^ 2 ≤ 0 := by linarith
    have h4 : ∀ j ∈ Finset.univ, (σ j * (w2 j - wb j)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp
        (le_antisymm h3 (Finset.sum_nonneg fun j _ => sq_nonneg _))
    ext j
    have := h4 j (Finset.mem_univ j)
    rcases mul_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this) with h5 | h5
    · exact absurd h5 (hσ j)
    · linarith
  · have := hC wb (g72wyb_wls_noconf H σ hσ h wb hwb)
    rw [hwb.1] at this
    exact this
