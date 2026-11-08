-- Prove2me | solution 1 for RobustToDynamics.step3_shrinkage_factor
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:49:22.515196+00:00
-- url     : https://prove2.me/submissions/f104ced4-4a4e-4362-a319-e0969efa77f8

import Mathlib
import Definitions.Def_RobustToDynamics_gamma

open Matrix

open RobustToDynamics in
theorem solution {n : ℕ} (G M : Matrix (Fin n) (Fin n) ℝ)
    (hL : Gᵀ * M * G - M = -1) (hM : M.PosDef) :
    (∀ i, 1 ≤ M i i) ∧ 0 ≤ gamma M ∧ gamma M < 1 ∧
      (gamma M • M - Gᵀ * M * G).PosSemidef := by
  have hGMG : Gᵀ * M * G = M - 1 := by
    have : Gᵀ * M * G = (Gᵀ * M * G - M) + M := by abel
    rw [this, hL]; abel
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    have := hM.1.apply j i
    rw [star_trivial] at this
    exact this
  have hpsd : (Gᵀ * M * G).PosSemidef := by
    have := hM.posSemidef.conjTranspose_mul_mul_same G
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hdiag : ∀ i, 1 ≤ M i i := by
    intro i
    have h1 := hpsd.diag_nonneg (i := i)
    rw [hGMG] at h1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h1
    linarith
  set R : ℝ := (if h : (Finset.univ : Finset (Fin n)).Nonempty then
      Finset.univ.sup' h (fun i => M i i + ∑ j ∈ Finset.univ.erase i, |M i j|) else 1) with hRdef
  have hRi : ∀ i, M i i + ∑ j ∈ Finset.univ.erase i, |M i j| ≤ R := by
    intro i
    have h : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ i⟩
    rw [hRdef, dif_pos h]
    exact Finset.le_sup' (fun i => M i i + ∑ j ∈ Finset.univ.erase i, |M i j|) (Finset.mem_univ i)
  have hR1 : 1 ≤ R := by
    by_cases h : (Finset.univ : Finset (Fin n)).Nonempty
    · obtain ⟨i, _⟩ := h
      have := hRi i
      have h2 : 0 ≤ ∑ j ∈ Finset.univ.erase i, |M i j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      linarith [hdiag i]
    · rw [hRdef, dif_neg h]
  have hRpos : 0 < R := by linarith
  have hgamma : gamma M = 1 - 1 / R := rfl
  refine ⟨hdiag, ?_, ?_, ?_⟩
  · rw [hgamma, sub_nonneg, div_le_one hRpos]; exact hR1
  · rw [hgamma]; have : 0 < 1 / R := by positivity
    linarith
  · rw [posSemidef_iff_dotProduct_mulVec]
    have hmat : gamma M • M - Gᵀ * M * G = 1 - (1 / R) • M := by
      rw [hGMG, hgamma, sub_smul, one_smul]; abel
    rw [hmat]
    constructor
    · apply IsHermitian.sub isHermitian_one
      unfold IsHermitian
      rw [conjTranspose_smul, hM.1.eq, star_trivial]
    · intro x
      simp only [star_trivial, sub_mulVec, one_mulVec, smul_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      -- Gershgorin-type bound
      have hrow : ∀ i, ∑ j, |M i j| ≤ R := by
        intro i
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), abs_of_pos (by linarith [hdiag i])]
        exact hRi i
      have hterm : ∀ i j, x i * (M i j * x j) ≤ |M i j| * (x i ^ 2 + x j ^ 2) / 2 := by
        intro i j
        have h1 : x i * (M i j * x j) ≤ |M i j| * |x i * x j| := by
          calc x i * (M i j * x j) = M i j * (x i * x j) := by ring
            _ ≤ |M i j * (x i * x j)| := le_abs_self _
            _ = |M i j| * |x i * x j| := abs_mul _ _
        have h2 : |x i * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
          rw [abs_mul]
          have := two_mul_le_add_sq |x i| |x j|
          rw [sq_abs, sq_abs] at this
          linarith
        calc x i * (M i j * x j) ≤ |M i j| * |x i * x j| := h1
          _ ≤ |M i j| * ((x i ^ 2 + x j ^ 2) / 2) :=
              mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
          _ = |M i j| * (x i ^ 2 + x j ^ 2) / 2 := by ring
      have hquad : x ⬝ᵥ (M *ᵥ x) ≤ R * (x ⬝ᵥ x) := by
        simp only [dotProduct, mulVec]
        calc ∑ i, x i * ∑ j, M i j * x j
            = ∑ i, ∑ j, x i * (M i j * x j) := by simp only [Finset.mul_sum]
          _ ≤ ∑ i, ∑ j, |M i j| * (x i ^ 2 + x j ^ 2) / 2 :=
              Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
          _ = ∑ i, x i ^ 2 * ∑ j, |M i j| := by
              have e1 : ∑ i, ∑ j, |M i j| * (x i ^ 2 + x j ^ 2) / 2
                  = (∑ i, ∑ j, |M i j| * x i ^ 2) / 2 + (∑ i, ∑ j, |M i j| * x j ^ 2) / 2 := by
                rw [← add_div, ← Finset.sum_add_distrib]
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl; intro i _
                rw [← Finset.sum_add_distrib, Finset.sum_div]
                apply Finset.sum_congr rfl; intro j _; ring
              have e2 : ∑ i, ∑ j, |M i j| * x j ^ 2 = ∑ i, ∑ j, |M i j| * x i ^ 2 := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro i _
                apply Finset.sum_congr rfl; intro j _
                rw [hsymm]
              rw [e1, e2]
              rw [add_halves]
              apply Finset.sum_congr rfl; intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro j _; ring
          _ ≤ ∑ i, x i ^ 2 * R :=
              Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _))
          _ = R * ∑ i, x i * x i := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      have : (1 / R) * (x ⬝ᵥ (M *ᵥ x)) ≤ x ⬝ᵥ x := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hRpos]
        linarith
      linarith
