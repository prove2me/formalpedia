-- Prove2me | solution 1 for WrightPDIPM.Termination.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T19:41:51.049984+00:00
-- url     : https://prove2.me/submissions/71d876be-93bd-4ef8-95e4-289f446fc6de

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

/-- Lemma A.4 (Stewart–Todd, p. 249): if `H ∈ ℝ^{p×q}` has full row rank, then
`χ(H) = sup_{Σ ∈ D₊} ‖ΣHᵀ(HΣHᵀ)⁻¹‖` is finite, where `D₊` is the set of diagonal matrices with
strictly positive diagonal and `‖·‖` is the operator norm induced by the Euclidean norm: there
is `K` with `‖ΣHᵀ(HΣHᵀ)⁻¹v‖ ≤ K‖v‖` for all `Σ ∈ D₊` and all `v`. -/
theorem solution {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) (hH : H.rank = p) :
    ∃ K : ℝ, ∀ σ : Fin q → ℝ, (∀ j, 0 < σ j) → ∀ v : Fin p → ℝ,
      norm2 ((diagonal σ * Hᵀ * (H * diagonal σ * Hᵀ)⁻¹) *ᵥ v) ≤ K * norm2 v := by
  obtain ⟨C, hC0, hC⟩ := g72wyb_core2 H
  refine ⟨C, fun σ hσ v => ?_⟩
  set M := H * diagonal σ * Hᵀ with hM
  have hnv : 0 ≤ norm2 v := Real.sqrt_nonneg _
  by_cases hdet : IsUnit M.det
  · set lam := M⁻¹ *ᵥ v with hlam
    set w := (diagonal σ * Hᵀ * M⁻¹) *ᵥ v with hw
    have hw' : w = diagonal σ *ᵥ (Hᵀ *ᵥ lam) := by
      rw [hw, hlam, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have hHw : H *ᵥ w = v := by
      rw [hw, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        ← hM, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hnc : g72wyb_NoConf H w := by
      intro z hz hconf
      by_contra hne
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have hwj : ∀ i, w i = σ i * (Hᵀ *ᵥ lam) i := by
        intro i; rw [hw']; simp [Matrix.mulVec_diagonal]
      have hterm : ∀ i, 0 ≤ z i * (Hᵀ *ᵥ lam) i := by
        intro i
        by_cases hi : z i = 0
        · simp [hi]
        · have := hconf i hi
          rw [hwj i] at this
          have h' : z i * (σ i * (Hᵀ *ᵥ lam) i) = σ i * (z i * (Hᵀ *ᵥ lam) i) := by ring
          rw [h'] at this
          exact (pos_of_mul_pos_right this (hσ i).le).le
      have hpos : 0 < z j * (Hᵀ *ᵥ lam) j := by
        have := hconf j hj
        rw [hwj j] at this
        have h' : z j * (σ j * (Hᵀ *ᵥ lam) j) = σ j * (z j * (Hᵀ *ᵥ lam) j) := by ring
        rw [h'] at this
        exact pos_of_mul_pos_right this (hσ j).le
      have hsum : 0 < z ⬝ᵥ (Hᵀ *ᵥ lam) :=
        Finset.sum_pos' (fun i _ => hterm i) ⟨j, Finset.mem_univ j, hpos⟩
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hz, zero_dotProduct] at hsum
      exact lt_irrefl _ hsum
    have := hC w hnc
    rw [hHw] at this
    exact this
  · have hinv : M⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit M hdet
    rw [hinv, Matrix.mul_zero, Matrix.zero_mulVec]
    unfold norm2
    simp only [Pi.zero_apply]
    norm_num
    exact mul_nonneg hC0 hnv
