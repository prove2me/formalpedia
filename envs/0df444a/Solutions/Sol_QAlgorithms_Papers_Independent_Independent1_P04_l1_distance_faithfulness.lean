-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.l1_distance_faithfulness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:53:00.449334+00:00
-- url     : https://prove2.me/submissions/ff16c21d-d17e-4b74-950c-921233c7dff5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P04
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.1,3, (2), (9): the entrywise-l1 minimum, nonnegativity and faithfulness. -/
theorem gk1_cand_eq {d : ℕ} (D : CoherenceMatrix d → CoherenceMatrix d → ℝ)
    (rho delta : CoherenceMatrix d) (hdelta : IncoherentState delta)
    (hmin : ∀ sigma, IncoherentState sigma → D rho delta ≤ D rho sigma) :
    distanceCandidate D rho = D rho delta := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨D rho delta, ?_⟩
      rintro v ⟨s, hs, rfl⟩
      exact hmin s hs
    · exact ⟨_, hdelta, rfl⟩
  · refine le_csInf ⟨D rho delta, delta, hdelta, rfl⟩ ?_
    rintro v ⟨s, hs, rfl⟩
    exact hmin s hs

theorem gk1_deph_inc {d : ℕ} (rho : CoherenceMatrix d) (hrho : IsDensityMatrix rho) :
    IncoherentState (dephasedMatrix rho) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold dephasedMatrix
    exact Matrix.PosSemidef.diagonal (fun i => hrho.1.diag_nonneg)
  · unfold dephasedMatrix
    rw [Matrix.trace_diagonal]
    exact hrho.2
  · intro i j hij
    simp [dephasedMatrix, Matrix.diagonal_apply, hij]

theorem gk1_off_le {d : ℕ} (rho delta : CoherenceMatrix d) (hd : BasisDiagonal delta) :
    Coherence.l1Coherence rho ≤ entrywiseDistance rho delta := by
  unfold Coherence.l1Coherence entrywiseDistance
  apply Finset.sum_le_sum
  intro i _
  calc ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖rho i j‖
      = ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖rho i j - delta i j‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hd i j (Finset.mem_filter.1 hj).2, sub_zero]
    _ ≤ ∑ j, ‖rho i j - delta i j‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)

theorem gk1_off_eq {d : ℕ} (rho : CoherenceMatrix d) :
    entrywiseDistance rho (dephasedMatrix rho) = Coherence.l1Coherence rho := by
  unfold Coherence.l1Coherence entrywiseDistance
  apply Finset.sum_congr rfl
  intro i _
  calc ∑ j, ‖rho i j - dephasedMatrix rho i j‖
      = ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖rho i j - dephasedMatrix rho i j‖ := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
        subst hj
        simp [dephasedMatrix]
    _ = ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖rho i j‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        have := (Finset.mem_filter.1 hj).2
        simp [dephasedMatrix, Matrix.diagonal_apply, this]

theorem solution :
    (∀ d, 0 < d → ∀ rho : CoherenceMatrix d, IsDensityMatrix rho →
      IncoherentState (dephasedMatrix rho) ∧
      entrywiseDistance rho (dephasedMatrix rho) = Coherence.l1Coherence rho ∧
      distanceCandidate entrywiseDistance rho = Coherence.l1Coherence rho ∧
      ∀ delta, IncoherentState delta → Coherence.l1Coherence rho ≤ entrywiseDistance rho delta) ∧
    CoherenceNonnegative (fun _ rho => Coherence.l1Coherence rho) ∧
    CoherenceFaithful (fun _ rho => Coherence.l1Coherence rho) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd rho hrho
    have hinc := gk1_deph_inc rho hrho
    have heq := gk1_off_eq rho
    refine ⟨hinc, heq, ?_, fun delta hdelta => gk1_off_le rho delta hdelta.2⟩
    rw [gk1_cand_eq _ rho _ hinc (fun s hs => heq ▸ gk1_off_le rho s hs.2), heq]
  · intro d hd rho hrho
    unfold Coherence.l1Coherence
    positivity
  · intro d hd rho hrho
    show Coherence.l1Coherence rho = 0 ↔ _
    unfold Coherence.l1Coherence
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)]
    constructor
    · intro h
      refine ⟨hrho, fun i j hij => ?_⟩
      have := h i (Finset.mem_univ _)
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)] at this
      exact norm_eq_zero.1 (this j (by simp [hij]))
    · intro h i _
      apply Finset.sum_eq_zero
      intro j hj
      rw [h.2 i j (Finset.mem_filter.1 hj).2, norm_zero]

