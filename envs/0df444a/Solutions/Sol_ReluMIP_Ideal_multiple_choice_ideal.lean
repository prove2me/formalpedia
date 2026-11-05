-- Prove2me | solution 1 for ReluMIP.Ideal.multiple_choice_ideal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:21:49.889303+00:00
-- url     : https://prove2.me/submissions/b3a302ed-e8fe-4e28-baa6-dbeb367eee32

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting
import Definitions.Def_ReluMIP_Ideal_Lifted5
import Theorems.Thm_ReluMIP_Ideal_fm_projection_eq_system7
import Theorems.Thm_ReluMIP_Ideal_system7c_redundant
import Theorems.Thm_ReluMIP_Ideal_relax6_eq_convexHull

namespace ReluMIP.Ideal

lemma wLb_le {η : ℕ} (w L U x : Fin η → ℝ) (hx : x ∈ box L U) (i : Fin η) :
    w i * Lbrev w L U i ≤ w i * x i := by
  obtain ⟨h1, h2⟩ := hx i
  unfold Lbrev
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h1 h
  · exact mul_le_mul_of_nonpos_left h2 (le_of_lt (not_le.mp h))

lemma le_wUb {η : ℕ} (w L U x : Fin η → ℝ) (hx : x ∈ box L U) (i : Fin η) :
    w i * x i ≤ w i * Ubrev w L U i := by
  obtain ⟨h1, h2⟩ := hx i
  unfold Ubrev
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h2 h
  · exact mul_le_mul_of_nonpos_left h1 (le_of_lt (not_le.mp h))

lemma mem_relax6_zero {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ)
    (hx : x ∈ box L U) (hf : affineFn w b x ≤ 0) : (x, (0 : ℝ), (0 : ℝ)) ∈ relax6 w b L U := by
  refine ⟨hf, ?_, hx, le_refl _, le_refl _, zero_le_one⟩
  intro I _
  simp only [rhs6b, sub_zero, mul_one, mul_zero, add_zero]
  exact Finset.sum_nonneg fun i _ => by
    have := wLb_le w L U x hx i
    nlinarith

lemma mem_relax6_one {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ)
    (hx : x ∈ box L U) (hf : 0 ≤ affineFn w b x) :
    (x, affineFn w b x, (1 : ℝ)) ∈ relax6 w b L U := by
  refine ⟨le_refl _, ?_, hx, hf, zero_le_one, le_refl _⟩
  intro I _
  simp only [rhs6b, sub_self, mul_zero, sub_zero, mul_one]
  have hs : ∑ i ∈ Finset.univ \ I, w i * x i + ∑ i ∈ I, w i * x i = ∑ i, w i * x i :=
    Finset.sum_sdiff (Finset.subset_univ I)
  have : ∑ i ∈ Finset.univ \ I, w i * x i ≤ ∑ i ∈ Finset.univ \ I, w i * Ubrev w L U i :=
    Finset.sum_le_sum fun i _ => le_wUb w L U x hx i
  unfold affineFn
  linarith

lemma relax6_zero {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ) (y : ℝ)
    (h : (x, y, (0 : ℝ)) ∈ relax6 w b L U) : y = 0 := by
  obtain ⟨_, h6b, _, hy, _⟩ := h
  have := h6b ∅ (Finset.empty_subset _)
  simp [rhs6b] at this
  linarith

lemma relax6_one {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ) (y : ℝ)
    (h : (x, y, (1 : ℝ)) ∈ relax6 w b L U) : y = affineFn w b x := by
  obtain ⟨h6a, h6b, _, _, _⟩ := h
  have := h6b (supp w) (subset_refl _)
  simp only [rhs6b, sub_self, mul_zero, sub_zero, mul_one] at this
  have h0 : ∑ i ∈ Finset.univ \ supp w, w i * Ubrev w L U i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have : w i = 0 := by simpa [supp] using hi
      simp [this]
  have h1 : ∑ i ∈ supp w, w i * x i = ∑ i, w i * x i :=
    Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      have : w i = 0 := by simpa [supp] using hi
      simp [this]
  simp only at h6a
  unfold affineFn at *
  linarith

theorem formulation6 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    IsFormulationFor (relax6 w b L U) (reluGraph w b L U) := by
  intro x y
  constructor
  · rintro ⟨hx, hy⟩
    simp only at hx hy
    rcases le_total (affineFn w b x) 0 with h | h
    · refine ⟨0, Or.inl rfl, ?_⟩
      have : y = 0 := by rw [hy, relu, max_eq_left h]
      rw [this]
      exact mem_relax6_zero w b L U x hx h
    · refine ⟨1, Or.inr rfl, ?_⟩
      have : y = affineFn w b x := by rw [hy, relu, max_eq_right h]
      rw [this]
      exact mem_relax6_one w b L U x hx h
  · rintro ⟨z, hz, hm⟩
    refine ⟨hm.2.2.1, ?_⟩
    have h6a : affineFn w b x ≤ y := hm.1
    have hy : 0 ≤ y := hm.2.2.2.1
    simp only
    rcases hz with rfl | rfl
    · have := relax6_zero w b L U x y hm
      subst this
      rw [relu, max_eq_left h6a]
    · have := relax6_one w b L U x y hm
      rw [relu, max_eq_right (this ▸ hy), this]

theorem relax5Lift_extreme {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    ∀ p ∈ Set.extremePoints ℝ (relax5Lift w b L U), p.1.2.2 = 0 ∨ p.1.2.2 = 1 := by
  rintro ⟨⟨x, y, z⟩, ⟨x0, x1, y0, y1⟩⟩ hp
  have hmem := hp.1
  obtain ⟨hx, hy, hy0, h5b, hy1, hy1p, h0, h1, hz0, hz1⟩ := hmem
  simp only at *
  rcases eq_or_lt_of_le hz0 with hz | hz
  · exact Or.inl hz.symm
  rcases eq_or_lt_of_le hz1 with hz' | hz'
  · exact Or.inr hz'
  left
  have h1z : 0 < 1 - z := by linarith
  set P0 : ((Fin η → ℝ) × ℝ × ℝ) × ((Fin η → ℝ) × (Fin η → ℝ) × ℝ × ℝ) :=
    (((1 - z)⁻¹ • x0, 0, 0), ((1 - z)⁻¹ • x0, 0, 0, 0)) with hP0
  set P1 : ((Fin η → ℝ) × ℝ × ℝ) × ((Fin η → ℝ) × (Fin η → ℝ) × ℝ × ℝ) :=
    ((z⁻¹ • x1, z⁻¹ * y1, 1), (0, z⁻¹ • x1, 0, z⁻¹ * y1)) with hP1
  have hm0 : P0 ∈ relax5Lift w b L U := by
    rw [hP0, relax5Lift, Set.mem_ofPred_eq]
    refine ⟨by simp, by simp, rfl, ?_, by simp, le_refl _, ?_, ?_, le_refl _, zero_le_one⟩
    · simp only [Pi.smul_apply, smul_eq_mul, sub_zero, mul_one]
      have : ∑ i, w i * ((1 - z)⁻¹ * x0 i) = (1 - z)⁻¹ * ∑ i, w i * x0 i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      have hinv : 0 < (1 - z)⁻¹ := inv_pos.mpr h1z
      have : (1 - z)⁻¹ * (∑ i, w i * x0 i + b * (1 - z)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hinv.le h5b
      have e : (1 - z)⁻¹ * (b * (1 - z)) = b := by field_simp
      nlinarith
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul, sub_zero, mul_one]
      obtain ⟨a1, a2⟩ := h0 i
      constructor
      · rw [← div_eq_inv_mul, le_div_iff₀ h1z]; exact a1
      · rw [← div_eq_inv_mul, div_le_iff₀ h1z]; exact a2
    · intro i; simp
  have hm1 : P1 ∈ relax5Lift w b L U := by
    rw [hP1, relax5Lift, Set.mem_ofPred_eq]
    refine ⟨by simp, by simp, rfl, by simp, ?_, ?_, ?_, ?_, zero_le_one, le_refl _⟩
    · simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      rw [hy1, mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · field_simp
    · exact mul_nonneg (inv_pos.mpr hz).le hy1p
    · intro i; simp
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      obtain ⟨a1, a2⟩ := h1 i
      constructor
      · rw [← div_eq_inv_mul, le_div_iff₀ hz]; exact a1
      · rw [← div_eq_inv_mul, div_le_iff₀ hz]; exact a2
  have hseg : (((x, y, z), (x0, x1, y0, y1)) :
      ((Fin η → ℝ) × ℝ × ℝ) × ((Fin η → ℝ) × (Fin η → ℝ) × ℝ × ℝ)) ∈
      openSegment ℝ P0 P1 := by
    refine ⟨1 - z, z, h1z, hz, by ring, ?_⟩
    simp only [hP0, hP1, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, zero_add,
      add_zero, mul_one, smul_zero, smul_smul]
    have hz0' : z ≠ 0 := hz.ne'
    have hz1' : 1 - z ≠ 0 := h1z.ne'
    rw [mul_inv_cancel₀ hz1', mul_inv_cancel₀ hz0', one_smul, one_smul, ← mul_assoc,
      mul_inv_cancel₀ hz0', one_mul]
    subst hx hy hy0
    simp
  have := hp.2 hm0 hm1 hseg
  have := congrArg (fun q => q.1.2.2) this
  simp only [hP0] at this
  exact this.symm

theorem relax5_eq_relax6' {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) : relax5 w b L U = relax6 w b L U := by
  rw [fm_projection_eq_system7 w b L U hLU]
  apply Set.Subset.antisymm
  · exact fun p hp => hp.1
  · exact fun p hp => ⟨hp, system7c_redundant w b L U p hp⟩

end ReluMIP.Ideal

open ReluMIP.Ideal in
theorem solution {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) :
    (∀ p ∈ Set.extremePoints ℝ (relax5Lift w b L U), p.1.2.2 = 0 ∨ p.1.2.2 = 1) ∧
      IsFormulationFor (relax5 w b L U) (reluGraph w b L U) ∧
      relax5 w b L U = convexHull ℝ {p | p ∈ relax5 w b L U ∧ (p.2.2 = 0 ∨ p.2.2 = 1)} := by
  refine ⟨relax5Lift_extreme w b L U, ?_, ?_⟩
  · rw [relax5_eq_relax6' w b L U hLU]
    exact formulation6 w b L U
  · rw [relax5_eq_relax6' w b L U hLU]
    exact relax6_eq_convexHull w b L U hLU
