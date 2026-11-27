-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_flagDegreeBound_7c0e09942d43
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:11:04.928707+00:00
-- url     : https://prove2.me/submissions/d3c8ff61-6b8e-45be-8de0-4424ab1aa14d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_bot_8fbec8549ade

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
open MvPolynomial NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : FlagDegreeBound.Statement := by
  intro K _ _ E r F _ _ hr i
  by_cases hi : (i : ℕ) = 0
  · have hrk : E.rank (F i) = 0 := by rw [hr i, hi]
    have hbot : F i = ⊥ := (Submodule.finrank_eq_zero (R := 𝓞 K) (S := F i)).mp hrk
    have hdeg : E.normDegree (F i) = 0 := by
      rw [HermitianBundle.normDegree, hbot, HermitianBundle.degree_bot, zero_div]
    rw [hdeg, hi]
    simp
  · have hne : F i ≠ ⊥ := by
      intro h
      apply hi
      rw [← hr i, h]
      simp [HermitianBundle.rank]
    have hle : ((E.slope (F i) : ℝ) : EReal) ≤ E.slopeMax :=
      le_iSup₂_of_le (F i) hne le_rfl
    have hipos : (0 : ℝ) < (i : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hi
    have hd : ((E.normDegree (F i) : ℝ) : EReal) =
        (((i : ℕ) : EReal)) * ((E.slope (F i) : ℝ) : EReal) := by
      have : E.normDegree (F i) = ((i : ℕ) : ℝ) * E.slope (F i) := by
        unfold HermitianBundle.slope
        rw [hr i]
        field_simp
      rw [this]
      simp
    rw [hd, ge_iff_le, EReal.neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
end GroundTheory.Heights₂.Heights
