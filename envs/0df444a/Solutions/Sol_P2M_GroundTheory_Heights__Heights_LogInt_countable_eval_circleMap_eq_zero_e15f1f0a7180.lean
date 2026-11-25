-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_countable_eval_circleMap_eq_zero_e15f1f0a7180
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:39.639844+00:00
-- url     : https://prove2.me/submissions/f3e66859-283d-41b4-9679-3bbda6b60ecf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_countable_circleMap_eq_5a39646ea44e

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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (P : Polynomial ℂ) (hP : P ≠ 0) :
    {θ : ℝ | P.eval (circleMap 0 1 θ) = 0}.Countable := by
  have hsub : {θ : ℝ | P.eval (circleMap 0 1 θ) = 0} ⊆
      ⋃ ρ ∈ P.roots.toFinset, {θ : ℝ | circleMap 0 1 θ = ρ} := by
    intro θ hθ
    simp only [mem_iUnion, mem_ofPred_eq]
    exact ⟨circleMap 0 1 θ, by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]; exact hθ, rfl⟩
  exact ((P.roots.toFinset.countable_toSet).biUnion fun ρ _ => countable_circleMap_eq ρ).mono hsub
end GroundTheory.Heights₂.Heights.LogInt
