-- Prove2me | solution 1 for QThermalClassical.eq_414
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T13:41:48.434177+00:00
-- url     : https://prove2.me/submissions/4d9316d6-2757-4326-83ab-41104f7122ed

import Mathlib

set_option autoImplicit false

open scoped ComplexOrder
open Matrix

theorem solution {d ι : Type} [Fintype d] [DecidableEq d] [Fintype ι]
    (C : ι → Matrix d d ℂ) (σ : Matrix d d ℂ)
    (hherm : ∀ i, (C i).IsHermitian) (hinv : ∀ i, C i * C i = 1)
    (hanti : ∀ i j, i ≠ j → C i * C j = -(C j * C i))
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    ∑ i, ((C i * σ).trace.re) ^ 2 ≤ 1 := by
  classical
  set a : ι → ℝ := fun i => (C i * σ).trace.re with ha
  have htrace_real : ∀ i, ((a i : ℂ)) = (C i * σ).trace := by
    intro i
    have hC : (C i).IsHermitian := hherm i
    have hσh : σ.IsHermitian := hσ.isHermitian
    have hstar : star ((C i * σ).trace) = (C i * σ).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hσh.eq, hC.eq,
        Matrix.trace_mul_comm]
    have h2 : (((C i * σ).trace.re : ℂ)) = (C i * σ).trace :=
      Complex.conj_eq_iff_re.mp hstar
    simpa [ha] using h2
  let S : Matrix d d ℂ := ∑ i, (a i : ℂ) • C i
  let c : ℝ := ∑ i, (a i) ^ 2
  have hcast : ((c : ℂ)) = ∑ i, (a i : ℂ) * (a i : ℂ) := by
    dsimp only [c]
    push_cast
    simp [pow_two]
  have hSherm : S.IsHermitian := by
    refine Finset.sum_induction _ _ (fun x y hx hy => hx.add hy) isHermitian_zero ?_
    intro i _
    refine (hherm i).smul ?_
    rw [isSelfAdjoint_iff]
    simp
  have hSS : S * S = (c : ℂ) • (1 : Matrix d d ℂ) := by
    have hterm : ∀ i j : ι, ((a i : ℂ) • C i) * ((a j : ℂ) • C j) =
        ((a i : ℂ) * (a j : ℂ)) • (C i * C j) := by
      intro i j
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hsplit : ∀ i : ι, (∑ j, ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) =
        ((a i : ℂ) * (a i : ℂ)) • (C i * C i) +
          ∑ j ∈ Finset.univ.erase i, ((a i : ℂ) * (a j : ℂ)) • (C i * C j) := by
      intro i
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      abel
    have hF1 : (∑ i, ∑ j, ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) =
        (∑ i, ((a i : ℂ) * (a i : ℂ)) • (C i * C i)) +
          ∑ i, ∑ j ∈ Finset.univ.erase i, ((a i : ℂ) * (a j : ℂ)) • (C i * C j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact hsplit i
    have hf : ∀ i j : ι, i ≠ j →
        ((a i : ℂ) * (a j : ℂ)) • (C i * C j) =
          - (((a j : ℂ) * (a i : ℂ)) • (C j * C i)) := by
      intro i j hij
      rw [hanti i j hij, smul_neg]
      congr 1
      rw [mul_comm (a i : ℂ) (a j : ℂ)]
    have hToff : (∑ j, ∑ i ∈ Finset.univ.erase j,
          ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          ((a i : ℂ) * (a j : ℂ)) • (C i * C j) := by
      have h1 : ∀ j : ι, (∑ i ∈ Finset.univ.erase j,
            ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) =
          (∑ i, ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) -
            ((a j : ℂ) * (a j : ℂ)) • (C j * C j) := by
        intro j
        rw [eq_sub_iff_add_eq]
        exact Finset.sum_erase_add _ _ (Finset.mem_univ j)
      have h2 : ∀ i : ι, (∑ j ∈ Finset.univ.erase i,
            ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) =
          (∑ j, ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) -
            ((a i : ℂ) * (a i : ℂ)) • (C i * C i) := by
        intro i
        rw [eq_sub_iff_add_eq]
        exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
      simp only [h1, h2]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_comm (f := fun x i => ((a i : ℂ) * (a x : ℂ)) • (C i * C x))]
    have hOneg : (∑ j, ∑ i ∈ Finset.univ.erase j,
          ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) =
        -(∑ i, ∑ j ∈ Finset.univ.erase i,
          ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) := by
      have hneg : ∀ j : ι, (∑ i ∈ Finset.univ.erase j,
            ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) =
          -∑ i ∈ Finset.univ.erase j, ((a j : ℂ) * (a i : ℂ)) • (C j * C i) := by
        intro j
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        exact hf i j (by simpa using hi)
      simp only [hneg]
      rw [← Finset.sum_neg_distrib]
    have hToffzero : (∑ i, ∑ j ∈ Finset.univ.erase i,
        ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) = 0 := by
      have h : (∑ i, ∑ j ∈ Finset.univ.erase i,
            ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) =
          -(∑ i, ∑ j ∈ Finset.univ.erase i,
            ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) := hToff.symm.trans hOneg
      have h2 : (2 : ℂ) • (∑ i, ∑ j ∈ Finset.univ.erase i,
            ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) = 0 := by
        rw [two_smul]
        nth_rw 1 [h]
        abel
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    have hT : (∑ i, ∑ j, ((a i : ℂ) * (a j : ℂ)) • (C i * C j)) =
        ∑ i, ((a i : ℂ) * (a i : ℂ)) • (C i * C i) := by
      rw [hF1, hToffzero, add_zero]
    calc S * S = (∑ i, (a i : ℂ) • C i) * (∑ j, (a j : ℂ) • C j) := rfl
      _ = ∑ i, ∑ j, ((a i : ℂ) • C i) * ((a j : ℂ) • C j) := by
            rw [Finset.sum_mul_sum]
      _ = ∑ i, ∑ j, ((a i : ℂ) * (a j : ℂ)) • (C i * C j) := by
            simp only [hterm]
      _ = ∑ i, ((a i : ℂ) * (a i : ℂ)) • (C i * C i) := hT
      _ = ∑ i, ((a i : ℂ) * (a i : ℂ)) • (1 : Matrix d d ℂ) := by
            simp only [hinv]
      _ = (∑ i, ((a i : ℂ) * (a i : ℂ))) • (1 : Matrix d d ℂ) := by
            rw [← Finset.sum_smul]
      _ = (c : ℂ) • (1 : Matrix d d ℂ) := by
            rw [← hcast]
  have htrS : (S * σ).trace = (c : ℂ) := by
    calc (S * σ).trace = ∑ i, (((a i : ℂ) • C i) * σ).trace := by
          rw [Finset.sum_mul, Matrix.trace_sum]
      _ = ∑ i, (a i : ℂ) * (C i * σ).trace := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Matrix.smul_mul, Matrix.trace_smul]
          rfl
      _ = ∑ i, (a i : ℂ) * (a i : ℂ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [htrace_real i]
      _ = (c : ℂ) := hcast.symm
  have htraceB : ((S - 1) * σ * (S - 1)).trace = 1 - (c : ℂ) := by
    have hexp : (S - 1) * σ * (S - 1) = S * σ * S - σ * S - S * σ + σ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
      simp only [Matrix.one_mul, Matrix.mul_one]
      abel
    have hcycle : (S * σ * S).trace = (c : ℂ) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm S (σ * S), Matrix.mul_assoc, hSS,
        Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, htr]
      simp
    have hSσ : (σ * S).trace = (S * σ).trace := Matrix.trace_mul_comm σ S
    rw [hexp]
    simp only [Matrix.trace_add, Matrix.trace_sub]
    rw [hcycle, hSσ, htrS, htr]
    ring
  have hpsd : ((S - 1) * σ * (S - 1)).PosSemidef := by
    have hB : (S - 1)ᴴ = S - 1 := by
      rw [Matrix.conjTranspose_sub, hSherm.eq, isHermitian_one.eq]
    have := hσ.mul_mul_conjTranspose_same (S - 1)
    simpa [hB] using this
  have hnn : (0 : ℂ) ≤ ((S - 1) * σ * (S - 1)).trace := hpsd.trace_nonneg
  rw [htraceB] at hnn
  have hre : (0 : ℝ) ≤ 1 - c := (Complex.le_def.mp hnn).1
  have hcle : c ≤ 1 := by linarith
  simpa [c] using hcle

