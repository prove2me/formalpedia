-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_RecordEigen_proof_71124cc634b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:03:47.789744+00:00
-- url     : https://prove2.me/submissions/f49ff65f-3807-427e-921d-5cfb0748548b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_logRd_nonneg_4800b4fb3388
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_abs_degree_sub_le_caf889cc4611
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_sum_primesB_le_b85d75dee8d5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
namespace RecordEigen
theorem _root_.solution (h₁ : PrimeLogSum.Statement) (h₂ : NormCountBound.Statement)
    (h₃ : DifferentExtNorm.Statement) : RecordEigen.Statement := by
  obtain ⟨C₅, h5⟩ := h₁
  refine ⟨max (2 * C₅) 1, ?_⟩
  intro E L _ _ _ _ Ψ _ ι j' B bad P hB hbad hcard hER hM
  have hd : (0 : ℝ) ≤ Module.finrank ℚ L := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ j' := Nat.cast_nonneg _
  have hD : ∀ τ, extDifferent (ι τ) ≠ ⊥ ∧
      Real.log (Ideal.absNorm (extDifferent (ι τ)) : ℝ) = Module.finrank ℚ L * logRd E :=
    fun τ => h₃ E L (ι τ)
  refine ⟨?_, ?_⟩
  · rw [mul_assoc]
    apply abs_degree_sub_le P P.record P.eig P.record_ne P.eig_ne (j' * logRd E)
    intro τ
    have hloc : LocalCountBound (P.record τ * (P.eig τ)⁻¹) (extDifferent (ι τ)) ∅ 0 j' := by
      intro p _ 𝔓 _
      rw [if_neg (Finset.notMem_empty p), zero_add]
      exact hER τ 𝔓
    have h := h₂ L _ _ ∅ 0 j' (mul_ne_zero (P.record_ne τ) (inv_ne_zero (P.eig_ne τ))) (hD τ).1 le_rfl hj hloc
    rw [(hD τ).2] at h
    calc _ ≤ _ := h
      _ = Module.finrank ℚ L * (j' * logRd E) := by ring
  · have hS := sum_primesB_le h5 hB hbad hcard
    have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
    have hR := logRd_nonneg E
    have key : |P.degree P.ht - P.degree P.record| ≤ Fintype.card Ψ * (j' * (2 * C₅ * Real.log B + logRd E)) := by
      apply abs_degree_sub_le P P.ht P.record P.ht_ne P.record_ne
      intro τ
      have h := h₂ L _ _ (primesB B bad) j' j' (mul_ne_zero (P.ht_ne τ) (inv_ne_zero (P.record_ne τ))) (hD τ).1 hj hj
        (hM τ)
      rw [(hD τ).2] at h
      calc _ ≤ _ := h
        _ ≤ Module.finrank ℚ L * (j' * (2 * C₅ * Real.log B)) + j' * (Module.finrank ℚ L * logRd E) := by
          gcongr
        _ = Module.finrank ℚ L * (j' * (2 * C₅ * Real.log B + logRd E)) := by ring
    have hM1 : 2 * C₅ * Real.log B ≤ max (2 * C₅) 1 * Real.log B :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hlogB
    have hM2 : logRd E ≤ max (2 * C₅) 1 * logRd E :=
      le_mul_of_one_le_left hR (le_max_right _ _)
    have hf : (0 : ℝ) ≤ Fintype.card Ψ * j' := mul_nonneg (Nat.cast_nonneg _) hj
    calc _ ≤ _ := key
      _ = (Fintype.card Ψ * j') * (2 * C₅ * Real.log B + logRd E) := by ring
      _ ≤ (Fintype.card Ψ * j') * (max (2 * C₅) 1 * Real.log B + max (2 * C₅) 1 * logRd E) := by
        gcongr
      _ = max (2 * C₅) 1 * (Fintype.card Ψ * j') * (Real.log B + logRd E) := by ring
end RecordEigen
end GroundTheory.Heights₂.Heights.NineStatements
