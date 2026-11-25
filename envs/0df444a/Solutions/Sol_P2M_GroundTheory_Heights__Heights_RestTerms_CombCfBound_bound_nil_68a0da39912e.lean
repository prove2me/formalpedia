-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_bound_nil_68a0da39912e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:17.672825+00:00
-- url     : https://prove2.me/submissions/f488153d-c9d9-4279-aa45-59083f1bdd88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_stair_strictAnti_db6e89d9b491
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_alt_of_strictAnti_30339c9c8742
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_vandermondeOf_X_eq_alt_52fd29888339


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Equiv Comb
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
namespace GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
theorem _root_.solution (m : ℕ) (lam : Fin m → ℕ) (hlam : Antitone lam) :
    |cf (fun i => lam i + stair m i) (alternantPsum m [])| ≤ ((latticeWords 0 lam).card : ℚ) := by
  have hA : alternantPsum m [] = alt (stair m) := by
    simp [alternantPsum, vandermondeOf_X_eq_alt]
  have hl : StrictAnti (fun i => lam i + stair m i) := fun i j h =>
    Nat.add_lt_add_of_le_of_lt (hlam h.le) (stair_strictAnti m h)
  rw [hA, cf_alt_of_strictAnti hl (stair_strictAnti m)]
  split_ifs with h
  · have h0 : lam = 0 := by
      funext i
      have := congrFun h i
      show lam i = 0
      omega
    subst h0
    have hne : (latticeWords 0 (0 : Fin m → ℕ)).Nonempty := by
      refine ⟨Fin.elim0, ?_⟩
      simp only [latticeWords, mem_filter, mem_univ, true_and]
      refine ⟨fun t _ i j _ => ?_, fun i => ?_⟩
      · simp [pcnt]
      · simp [pcnt]
    rw [abs_one, Nat.one_le_cast]
    exact Finset.card_pos.mpr hne
  · simp
end GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
