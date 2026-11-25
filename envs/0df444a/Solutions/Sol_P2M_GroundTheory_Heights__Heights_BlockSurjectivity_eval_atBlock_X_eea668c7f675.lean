-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_eval_atBlock_X_eea668c7f675
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:28.629806+00:00
-- url     : https://prove2.me/submissions/7bc70a87-1582-40af-919f-4e639e1d6db2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_self_90c3898f7ac0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_withBlock_of_ne_12930e8adeee

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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (x : Coord n → ℂ) (v : Coord n) :
    eval x (atBlock k₀ w (X v)) = withBlock k₀ (w ()) x v.1 v.2 := by
  rcases v with ⟨k, i⟩
  by_cases h : k = k₀
  · subst h
    simp [atBlock, sepBlock, evalBlock, withBlock_self]
  · simp [atBlock, sepBlock, h, withBlock_of_ne h]
end GroundTheory.Heights₂.Heights.BlockSurjectivity
