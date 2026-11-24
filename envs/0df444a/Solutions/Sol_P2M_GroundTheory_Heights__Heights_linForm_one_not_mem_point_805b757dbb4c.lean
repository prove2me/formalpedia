-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:20.860936+00:00
-- url     : https://prove2.me/submissions/4eae25c5-c710-40e5-ade4-087ea1fb3b15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (F : Type*) [Field F] :
    linForm (fun _ => (1 : F)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) F)) := by
  rw [Ideal.mem_bot]
  simp [linForm, X_ne_zero]
end GroundTheory.Heights₂.Heights
