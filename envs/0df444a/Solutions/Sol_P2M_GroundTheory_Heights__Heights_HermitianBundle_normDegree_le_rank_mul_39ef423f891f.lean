-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianBundle_normDegree_le_rank_mul_39ef423f891f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:55:58.488842+00:00
-- url     : https://prove2.me/submissions/fbdbbd49-082e-4d2c-a2fb-d5803a06aac2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DegreeTopEqArithDegree
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
open NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace HermitianBundle
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (E : HermitianBundle.{0} K) (G : Submodule (𝓞 K) E.carrier) (m : ℝ)
    (hm : E.slopeMax ≤ (m : EReal)) : E.normDegree G ≤ E.rank G * m := by
  by_cases hr : E.rank G = 0
  · have hbot : G = ⊥ := (Submodule.finrank_eq_zero (R := 𝓞 K) (S := G)).mp hr
    rw [hr, HermitianBundle.normDegree, hbot, HermitianBundle.degree_bot]
    simp
  · have hne : G ≠ ⊥ := by
      rintro rfl
      apply hr
      simp [HermitianBundle.rank]
    have hle : ((E.slope G : ℝ) : EReal) ≤ E.slopeMax := le_iSup₂_of_le G hne le_rfl
    have hs : E.slope G ≤ m := EReal.coe_le_coe_iff.mp (hle.trans hm)
    have hrpos : (0 : ℝ) < E.rank G := by exact_mod_cast Nat.pos_of_ne_zero hr
    have heq : E.normDegree G = E.rank G * E.slope G := by
      unfold HermitianBundle.slope
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hs hrpos.le
end HermitianBundle
end GroundTheory.Heights₂.Heights
