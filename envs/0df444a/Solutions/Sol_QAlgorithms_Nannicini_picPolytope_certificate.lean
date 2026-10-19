-- Prove2me | solution 1 for QAlgorithms.Nannicini.picPolytope_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:49:09.841654+00:00
-- url     : https://prove2.me/submissions/32b3d651-7e09-4498-b179-8fa24319821c

import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_QAlgorithms_Nannicini_Ch08a_Model
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open QAlgorithms QAlgorithms.SDP
open scoped ComplexOrder

private lemma scalar_alternative {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) :
    (∃ z : ℝ, 0 ≤ z ∧ ∀ i, a i * z ≤ b i) ∨
    (∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ 0 ≤ ∑ i, a i * y i ∧ ∑ i, b i * y i < 0) := by
  classical
  by_cases hb : ∀ i, 0 ≤ b i
  · exact Or.inl ⟨0, le_rfl, by simpa using hb⟩
  push Not at hb
  obtain ⟨j, hj⟩ := hb
  by_cases hbad : ∃ j, 0 ≤ a j ∧ b j < 0
  · obtain ⟨j, haj, hbj⟩ := hbad
    right
    refine ⟨Pi.single j 1, ?_, ?_, ?_⟩
    · intro i; by_cases hi : i = j <;> simp [hi]
    · simpa [Pi.single_apply] using haj
    · simpa [Pi.single_apply] using hbj
  have hneg (i : ι) (hi : b i < 0) : a i < 0 := by
    by_contra h; exact hbad ⟨i, le_of_not_gt h, hi⟩
  let f : ι → ℝ := fun i => if a i < 0 then b i / a i else 0
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hpos : 0 < f j := by simp [f, hneg j hj]; exact div_pos_of_neg_of_neg hj (hneg j hj)
  have hkpos : 0 < f k := lt_of_lt_of_le hpos (hk j (Finset.mem_univ _))
  have hak : a k < 0 := by by_contra h; simp [f, h] at hkpos
  have hf : f k = b k / a k := by simp [f, hak]
  have heq : a k * f k = b k := by rw [hf]; field_simp [ne_of_lt hak]
  by_cases hz : ∀ i, a i * f k ≤ b i
  · exact Or.inl ⟨f k, le_of_lt hkpos, hz⟩
  push Not at hz
  obtain ⟨i, hi⟩ := hz
  have hai : 0 < a i := by
    by_contra h
    have hle : a i ≤ 0 := le_of_not_gt h
    rcases lt_or_eq_of_le hle with hlt | he
    · have hh := hk i (Finset.mem_univ _)
      have hh' : b i / a i ≤ f k := by simpa [f, hlt] using hh
      have hh'' := (div_le_iff_of_neg hlt).mp hh'
      nlinarith
    · have hbi : b i < 0 := by simpa [he] using hi
      exact hbad ⟨i, by simp [he], hbi⟩
  right
  refine ⟨fun j => (-a k) * (Pi.single i (1 : ℝ) : ι → ℝ) j + a i * (Pi.single k (1 : ℝ) : ι → ℝ) j, ?_, ?_, ?_⟩
  · intro j
    apply add_nonneg
    · apply mul_nonneg (by linarith); by_cases h : j = i <;> simp [h]
    · apply mul_nonneg (le_of_lt hai); by_cases h : j = k <;> simp [h]
  · simp [mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_comm]
  · have hh := mul_lt_mul_of_pos_left hi (neg_pos.mpr hak)
    have hb : b k = a k * f k := heq.symm
    simp only [mul_add, Finset.sum_add_distrib]
    simp [mul_comm, Pi.single_apply]
    nlinarith

private lemma trace_combination {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (C X : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → ℝ) :
    ((∑ j, (y j : ℂ) • A j - C) * X).trace.re =
      ∑ j, (A j * X).trace.re * y j - (C * X).trace.re := by
  simp [Matrix.sub_mul, Matrix.sum_mul, Matrix.trace_sub,
    Matrix.trace_sum, Matrix.trace_smul, Complex.mul_re, mul_comm]

private lemma certificate_alternative {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (c γ ε : ℝ) (hε : 0 < ε)
    (hbase : ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ c - ε ≤ ∑ i, a i * w i) :
    (∃ z : ℝ, 0 ≤ z ∧ (∀ i, a i * z ≤ b i) ∧ γ ≤ c * z) ∨
    (∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ ∑ i, b i * y i ≤ γ ∧
      c - ε ≤ ∑ i, a i * y i) := by
  classical
  let a' : Option ι → ℝ := fun i => i.elim (-c) a
  let b' : Option ι → ℝ := fun i => i.elim (-γ) b
  rcases scalar_alternative a' b' with ⟨z, hz, hzi⟩ | ⟨v, hv, ha, hb⟩
  · left
    exact ⟨z, hz, fun i => hzi (some i), by have hh := hzi none; dsimp [a', b'] at hh; linarith⟩
  have ha' : c * v none ≤ ∑ i, a i * v (some i) := by
    simpa [a', Fintype.sum_option] using ha
  have hb' : ∑ i, b i * v (some i) < γ * v none := by
    simpa [b', Fintype.sum_option] using hb
  right
  by_cases hμ : 0 < v none
  · refine ⟨fun i => v (some i) / v none, fun i => div_nonneg (hv _) (le_of_lt hμ), ?_, ?_⟩
    · simp_rw [← mul_div_assoc]; rw [← Finset.sum_div]
      exact le_of_lt ((div_lt_iff₀ hμ).mpr hb')
    · simp_rw [← mul_div_assoc]; rw [← Finset.sum_div]
      have hh := (le_div_iff₀ hμ).mpr ha'
      linarith
  · have hzero : v none = 0 := le_antisymm (le_of_not_gt hμ) (hv _)
    rw [hzero, mul_zero] at ha' hb'
    obtain ⟨w, hw, hwa⟩ := hbase
    let B := ∑ i, b i * v (some i)
    let W := ∑ i, b i * w i
    let t := max 0 ((W - γ) / (-B))
    have ht : 0 ≤ t := le_max_left _ _
    have htb : W - γ ≤ t * (-B) :=
      (div_le_iff₀ (neg_pos.mpr hb')).mp (le_max_right _ _)
    refine ⟨fun i => t * v (some i) + w i,
      fun i => add_nonneg (mul_nonneg ht (hv _)) (hw _), ?_, ?_⟩
    · simp only [mul_add, Finset.sum_add_distrib]
      simp_rw [mul_left_comm (b _) t, ← Finset.mul_sum]
      change t * B + W ≤ γ
      nlinarith
    · simp only [mul_add, Finset.sum_add_distrib]
      simp_rw [mul_left_comm (a _) t, ← Finset.mul_sum]
      have hh := mul_nonneg ht ha'
      linarith

theorem solution {n m : ℕ} (hm : 0 < m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (b : Fin m → ℝ) (C : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (_hAherm : ∀ j, (A j).IsHermitian) (_hCherm : C.IsHermitian)
    (hA1 : A ⟨0, hm⟩ = 1) (_hb1 : b ⟨0, hm⟩ = R) (_hR : 0 < R) (_hC : specNorm C ≤ 1)
    (γ ε : ℝ) (hε : 0 < ε) (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosSemidef) :
    (picPolytope A b C γ ε X = ∅ →
      ∃ z : ℝ, 0 ≤ z ∧ PrimalFeasible A b ((z : ℂ) • X) ∧
        γ ≤ (C * ((z : ℂ) • X)).trace.re) ∧
    ((picPolytope A b C γ ε X).Nonempty →
      ¬ PrimalFeasible A b X ∨ (C * X).trace.re ≤ γ + ε) := by
  classical
  let a : Fin m → ℝ := fun j => (A j * X).trace.re
  let c : ℝ := (C * X).trace.re
  have hbase : ∃ w : Fin m → ℝ, (∀ j, 0 ≤ w j) ∧ c - ε ≤ ∑ j, a j * w j := by
    by_cases hzero : X = 0
    · refine ⟨0, by simp, ?_⟩
      simp [a, c, hzero]; linarith
    · have ht := Complex.nonneg_iff.mp hX.trace_nonneg
      have htr : 0 < X.trace.re := by
        refine lt_of_le_of_ne ht.1 ?_
        intro hz
        apply hzero
        apply hX.trace_eq_zero_iff.mp
        apply Complex.ext <;> simp [hz.symm, ht.2.symm]
      have ha0 : a ⟨0, hm⟩ = X.trace.re := by simp [a, hA1]
      let t := max 0 (c / X.trace.re)
      have ht0 : 0 ≤ t := le_max_left _ _
      refine ⟨Pi.single ⟨0, hm⟩ t, ?_, ?_⟩
      · intro j; by_cases hj : j = ⟨0, hm⟩ <;> simp [hj, ht0]
      · simp only [Pi.single_apply]
        simp [ha0]
        have hh : c ≤ t * X.trace.re := (div_le_iff₀ htr).mp (le_max_right _ _)
        nlinarith
  have hscale (D : Matrix (Fin n) (Fin n) ℂ) (z : ℝ) :
      (D * ((z : ℂ) • X)).trace.re = (D * X).trace.re * z := by
    simp [Matrix.trace_smul, Complex.mul_re, mul_comm]
  constructor
  · intro hempty
    rcases certificate_alternative a b c γ ε hε hbase with ⟨z, hz, hza, hzc⟩ | ⟨y, hy, hyb, hya⟩
    · refine ⟨z, hz, ⟨?_, ?_⟩, ?_⟩
      · exact hX.smul (Complex.nonneg_iff.mpr ⟨hz, by simp⟩)
      · intro j; rw [hscale]; exact hza j
      · rw [hscale]; exact hzc
    · have hyP : y ∈ picPolytope A b C γ ε X := by
        refine ⟨hyb, ?_, hy⟩
        rw [trace_combination]
        change -ε ≤ (∑ j, a j * y j) - c
        linarith
      rw [hempty] at hyP
      exact False.elim (Set.notMem_empty _ hyP)
  · rintro ⟨y, hyb, hya, hy⟩
    by_cases hf : PrimalFeasible A b X
    · right
      rw [trace_combination] at hya
      have hh : ∑ j, (A j * X).trace.re * y j ≤ ∑ j, b j * y j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hf.2 j) (hy j)
      linarith
    · exact Or.inl hf
