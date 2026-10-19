-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.modularExpansion_universal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:12:26.293545+00:00
-- url     : https://prove2.me/submissions/f25ac845-b147-4eff-b6f7-76a5003595dd

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
set_option autoImplicit false

/-!
# Fast and fault-tolerant logical measurements (arXiv:2510.14895v1)

Paper-local definitions and statement-only targets. Deferred nodes are recorded in the
assigned unit's HARD.md and GAPS.json. No operational fault-distance lower bound is
inferred from the open-boundary homology calculation.
-/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P06
/-- Lemma 7.9, PDF p.37: containment of ker(G transpose) in W suffices. -/


theorem solution {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (W : Submodule F2 (V → F2)) (t : ℝ) (positive : 0 < t)
    (kernel : LinearMap.ker G.transpose.mulVecLin ≤ W) :
    HasModularExpansion G W t t⁻¹ := by
  refine ⟨positive, fun v => ?_⟩
  by_cases h : G.transpose.mulVec v = 0
  · have hv : v ∈ W := kernel (by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact h)
    have hr : restrictVertices (addressed W) v = v := by
      funext j
      unfold restrictVertices
      split_ifs with hj
      · rfl
      · by_contra hne
        exact hj (by simp only [addressed, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨v, hv, Ne.symm hne⟩)
    have hw : modularCosetWeight W (restrictVertices (addressed W) v) = 0 := by
      rw [hr]
      apply Nat.eq_zero_of_le_zero
      unfold modularCosetWeight
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ (⟨-v, W.neg_mem hv⟩ : W))) ?_
      simp
    rw [hw]
    simp [min_eq_right positive.le]
  · have h1 : (1 : ℝ) ≤ hammingNorm (G.transpose.mulVec v) := by
      have := hammingNorm_pos_iff.mpr h
      exact_mod_cast this
    have h2 : t⁻¹ * min t (modularCosetWeight W (restrictVertices (addressed W) v) : ℝ) ≤ 1 := by
      calc t⁻¹ * min t _ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left (min_le_left _ _) (inv_nonneg.mpr positive.le)
        _ = 1 := inv_mul_cancel₀ positive.ne'
    linarith

