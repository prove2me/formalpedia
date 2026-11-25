-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_pivotAlg_58997dd4a21b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:10:01.809598+00:00
-- url     : https://prove2.me/submissions/1e49722d-fff0-4b32-b4bb-631f33eec52b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isAlgebraic_flagMinor_2606086a539a

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (h₁ : FlagPivotIdentity.Statement)
    (hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0) :
    Algebra.IsAlgebraic (pivotAlg F n) (flagMinorAlg F n) := by
  constructor
  rintro ⟨y, hy⟩
  induction hy using Algebra.adjoin_induction with
  | mem y hy' =>
    obtain ⟨q, rfl⟩ := hy'
    exact isAlgebraic_flagMinor F n h₁ hne q
  | algebraMap r => exact isAlgebraic_algebraMap (algebraMap F (pivotAlg F n) r)
  | add y z hy hz ihy ihz =>
    have e : (⟨y + z, add_mem hy hz⟩ : flagMinorAlg F n) = ⟨y, hy⟩ + ⟨z, hz⟩ := Subtype.ext rfl
    rw [e]
    exact ihy.add ihz
  | mul y z hy hz ihy ihz =>
    have e : (⟨y * z, mul_mem hy hz⟩ : flagMinorAlg F n) = ⟨y, hy⟩ * ⟨z, hz⟩ := Subtype.ext rfl
    rw [e]
    exact ihy.mul ihz
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
