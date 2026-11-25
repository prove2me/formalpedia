-- Prove2me | solution 1 for PositivityTheory.RL.Up.eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:30.413977+00:00
-- url     : https://prove2.me/submissions/7195d938-137c-4d3e-8ee5-a4d789b95a73

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
namespace PositivityTheory.RL.Up
theorem _root_.solution {β : Type} [Fintype β] [DecidableEq β] (ξ : Matrix β β ℂ →ₗ[ℂ] ℂ)
    (h : ∀ A B, ξ (A * B - B * A) = 0) : ∃ c : ℂ, ∀ A, ξ A = c * A.trace := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨b⟩⟩
  · exact ⟨0, fun A => by rw [Subsingleton.elim A 0, map_zero, zero_mul]⟩
  refine ⟨ξ (single b b 1), fun A => ?_⟩
  have h1 : ∀ i j, i ≠ j → ξ (single i j 1) = 0 := fun i j hij => by
    have := h (single i i 1) (single i j 1)
    rwa [single_mul_single_same, single_mul_single_of_ne (h := hij.symm), one_mul, sub_zero] at this
  have h2 : ∀ i, ξ (single i i 1) = ξ (single b b 1) := fun i => by
    have := h (single i b 1) (single b i 1)
    rwa [single_mul_single_same, single_mul_single_same, one_mul, map_sub, sub_eq_zero] at this
  conv_lhs => rw [matrix_eq_sum_single A]
  simp only [map_sum]
  rw [Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ j, ξ (single i j (A i j)) = A i j * ξ (single i j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [e, h1 i j hj.symm, mul_zero]) (by simp), e, h2, mul_comm]
  rfl
end PositivityTheory.RL.Up
