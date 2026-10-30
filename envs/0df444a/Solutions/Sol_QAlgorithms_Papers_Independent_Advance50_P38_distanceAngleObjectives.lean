-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.distanceAngleObjectives
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:11:56.721775+00:00
-- url     : https://prove2.me/submissions/d526e8e3-e994-43da-9f6a-2d76dd3bcaf7

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38
open scoped BigOperators Topology Manifold ContDiff

noncomputable section

theorem s109_59_frobSq_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    frobSq M = (Matrix.trace (M.conjTranspose * M)).re := by
  simp only [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re]

theorem s109_59_dist {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U.conjTranspose * U = 1) :
    frobSq (U * A * U.conjTranspose - C) =
      frobSq A + frobSq C - 2 * realTraceOverlap A C U := by
  rw [s109_59_frobSq_eq, s109_59_frobSq_eq, s109_59_frobSq_eq, realTraceOverlap]
  have e1 : Matrix.trace ((U * A * U.conjTranspose).conjTranspose * (U * A * U.conjTranspose)) =
      Matrix.trace (A.conjTranspose * A) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have : U * A.conjTranspose * U.conjTranspose * (U * A * U.conjTranspose) =
        U * (A.conjTranspose * A) * U.conjTranspose := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul]
    simp only [Matrix.mul_assoc] at this ⊢
    rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc]
    simp only [Matrix.mul_assoc, hU, Matrix.mul_one]
  have e2 : Matrix.trace ((U * A * U.conjTranspose).conjTranspose * C) =
      star (Matrix.trace (C.conjTranspose * (U * A * U.conjTranspose))) := by
    rw [← Matrix.trace_conjTranspose]
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, e1, e2]
  simp only [Complex.sub_re, Complex.star_def, Complex.conj_re]
  ring

theorem solution {n : ℕ} (hn : 0 < n) (A C : (Matrix (Fin n) (Fin n) ℂ)) :
    (∀ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      frobSq ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose - C) =
        frobSq A + frobSq C - 2 * realTraceOverlap A C U) ∧
    (∀ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      (∀ V : Matrix.specialUnitaryGroup (Fin n) ℂ,
        frobSq ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose - C) ≤
          frobSq ((V : (Matrix (Fin n) (Fin n) ℂ)) * A * (V : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose - C)) ↔
      ∀ V : Matrix.specialUnitaryGroup (Fin n) ℂ, realTraceOverlap A C V ≤ realTraceOverlap A C U) ∧
    (A ≠ 0 → C ≠ 0 → ∀ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      (∀ V : Matrix.specialUnitaryGroup (Fin n) ℂ, lineCosSq A C V ≤ lineCosSq A C U) ↔
      ∀ V : Matrix.specialUnitaryGroup (Fin n) ℂ,
        ‖Matrix.trace (C.conjTranspose * ((V : (Matrix (Fin n) (Fin n) ℂ)) * A * (V : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))‖ ≤
        ‖Matrix.trace (C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))‖) ∧
    (∀ R : ℝ, 0 ≤ R →
      {z : ℂ | ∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
        z = Matrix.trace (C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))} =
        {z : ℂ | ‖z‖ ≤ R} →
      ∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
        realTraceOverlap A C U = numericalRadius A C) := by
  have hd : ∀ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      frobSq ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose - C) =
        frobSq A + frobSq C - 2 * realTraceOverlap A C U := by
    intro U
    apply s109_59_dist
    exact Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
  have hpos : ∀ M : Matrix (Fin n) (Fin n) ℂ, M ≠ 0 → 0 < frobSq M := by
    intro M hM
    obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hM (Matrix.ext h)
    unfold frobSq
    have h1 : 0 < Complex.normSq (M i j) := Complex.normSq_pos.mpr hij
    calc (0 : ℝ) < Complex.normSq (M i j) := h1
      _ ≤ ∑ j', Complex.normSq (M i j') :=
          Finset.single_le_sum (f := fun j' => Complex.normSq (M i j'))
            (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', Complex.normSq (M i' j') :=
          Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (M i' j'))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  refine ⟨hd, ?_, ?_, ?_⟩
  · intro U
    constructor
    · intro h V
      have := h V
      rw [hd, hd] at this
      linarith
    · intro h V
      rw [hd, hd]
      linarith [h V]
  · intro hA hC U
    have hden : 0 < frobSq A * frobSq C := mul_pos (hpos A hA) (hpos C hC)
    have key : ∀ V : Matrix.specialUnitaryGroup (Fin n) ℂ, lineCosSq A C V =
        ‖Matrix.trace (C.conjTranspose * ((V : (Matrix (Fin n) (Fin n) ℂ)) * A *
          (V : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))‖ ^ 2 / (frobSq A * frobSq C) := by
      intro V
      rw [lineCosSq, Complex.sq_norm]
    constructor
    · intro h V
      have := h V
      rw [key, key, div_le_div_iff_of_pos_right hden] at this
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
    · intro h V
      rw [key, key, div_le_div_iff_of_pos_right hden]
      exact pow_le_pow_left₀ (norm_nonneg _) (h V) 2
  · intro R hR hset
    have hmem : (R : ℂ) ∈ {z : ℂ | ‖z‖ ≤ R} := by
      simp [abs_of_nonneg hR]
    rw [← hset] at hmem
    obtain ⟨U, hU⟩ := hmem
    refine ⟨U, ?_⟩
    have hrad : numericalRadius A C = R := by
      unfold numericalRadius
      apply IsGreatest.csSup_eq
      refine ⟨⟨U, by rw [← hU]; simp [abs_of_nonneg hR]⟩, ?_⟩
      rintro r ⟨V, rfl⟩
      have : Matrix.trace (C.conjTranspose * ((V : (Matrix (Fin n) (Fin n) ℂ)) * A *
          (V : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose)) ∈ {z : ℂ | ‖z‖ ≤ R} := by
        rw [← hset]; exact ⟨V, rfl⟩
      exact this
    rw [hrad, realTraceOverlap, ← hU]
    simp

end
