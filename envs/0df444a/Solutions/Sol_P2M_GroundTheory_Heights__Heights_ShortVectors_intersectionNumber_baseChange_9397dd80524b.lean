-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ShortVectors_intersectionNumber_baseChange_9397dd80524b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:38.908593+00:00
-- url     : https://prove2.me/submissions/1714aeba-e59f-4070-94e4-d946e6fedf04

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_pow_le_covolume_f25d525c2258
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_finite_ball_944d5e9d2efe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_exists_isLeast_a128e7cb936c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_card_le_562b29c82b98

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ShortVectors
theorem _root_.solution : ShortVectors.Statement := by
  intro n hn L _ _
  obtain ⟨lam, hlam, hleast⟩ := KShort.exists_isLeast hn L
  have hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖ := fun v hv hv0 => hleast.2 ⟨v, hv, hv0, rfl⟩
  refine ⟨lam, hleast, KShort.pow_le_covolume hn L hlam hmin, ?_⟩
  intro U r hr
  have hfin : {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0}.Finite :=
    (KShort.finite_ball L r).subset fun v hv => ⟨hv.1, hv.2.2.1⟩
  refine ⟨hfin, ?_⟩
  have hcard := KShort.card_le L U hlam hr hmin
  have heq : {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r} =
      insert 0 {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0} := by
    ext v
    by_cases h : v = 0
    · subst h
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, true_or, iff_true]
      exact ⟨L.zero_mem, U.zero_mem, by simp; linarith⟩
    · simp [h]
  rw [heq, Set.ncard_insert_of_notMem (by simp) hfin] at hcard
  push_cast at hcard
  linarith
end ShortVectors
end GroundTheory.Heights₂.Heights
