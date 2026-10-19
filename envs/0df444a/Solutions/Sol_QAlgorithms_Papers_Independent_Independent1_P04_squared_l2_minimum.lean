-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.squared_l2_minimum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:51:57.874229+00:00
-- url     : https://prove2.me/submissions/ff57cf07-1124-4166-8b86-2790b4ad615b

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

/-- PDF pp.3,10, (10), (G.1): squared Hilbert–Schmidt minimum; both off-diagonal orders count. -/
theorem gk_cand_eq {d : ℕ} (D : CoherenceMatrix d → CoherenceMatrix d → ℝ)
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

theorem gk_deph_inc {d : ℕ} (rho : CoherenceMatrix d) (hrho : IsDensityMatrix rho) :
    IncoherentState (dephasedMatrix rho) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold dephasedMatrix
    exact Matrix.PosSemidef.diagonal (fun i => hrho.1.diag_nonneg)
  · unfold dephasedMatrix
    rw [Matrix.trace_diagonal]
    exact hrho.2
  · intro i j hij
    simp [dephasedMatrix, Matrix.diagonal_apply, hij]

theorem gk_off_le {d : ℕ} (rho delta : CoherenceMatrix d) (hd : BasisDiagonal delta) :
    squaredOffDiagonal rho ≤ squaredHSDistance rho delta := by
  unfold squaredOffDiagonal squaredHSDistance
  apply Finset.sum_le_sum
  intro i _
  calc ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖rho i j‖^2
      = ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖rho i j - delta i j‖^2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hd i j (Finset.mem_filter.1 hj).2, sub_zero]
    _ ≤ ∑ j, ‖rho i j - delta i j‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)

theorem gk_off_eq {d : ℕ} (rho : CoherenceMatrix d) :
    squaredHSDistance rho (dephasedMatrix rho) = squaredOffDiagonal rho := by
  unfold squaredOffDiagonal squaredHSDistance
  apply Finset.sum_congr rfl
  intro i _
  calc ∑ j, ‖rho i j - dephasedMatrix rho i j‖^2
      = ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖rho i j - dephasedMatrix rho i j‖^2 := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
        subst hj
        simp [dephasedMatrix]
    _ = ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), ‖rho i j‖^2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have := (Finset.mem_filter.1 hj).2
        simp [dephasedMatrix, Matrix.diagonal_apply, this]

theorem solution (d : ℕ) (hd : 0 < d) (rho : CoherenceMatrix d)
    (hrho : IsDensityMatrix rho) :
    IncoherentState (dephasedMatrix rho) ∧
    squaredHSDistance rho (dephasedMatrix rho) = squaredOffDiagonal rho ∧
    distanceCandidate squaredHSDistance rho = squaredOffDiagonal rho ∧
    ∀ delta, IncoherentState delta → squaredOffDiagonal rho ≤ squaredHSDistance rho delta := by
  have hinc := gk_deph_inc rho hrho
  have heq := gk_off_eq rho
  refine ⟨hinc, heq, ?_, fun delta hdelta => gk_off_le rho delta hdelta.2⟩
  rw [gk_cand_eq _ rho _ hinc (fun s hs => heq ▸ gk_off_le rho s hs.2), heq]

