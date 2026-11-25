-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_hilbFn_map_ba3c10076c2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:07:26.062283+00:00
-- url     : https://prove2.me/submissions/054900e4-a331-46b8-8f88-20e14c848bd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_gradedPiece_map_d80caa80bd95

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (I : Ideal (MRing ι F)) (m : K → ℤ) :
    hilbFn (I.map (map (algebraMap F F'))) m = hilbFn I m := by
  unfold hilbFn
  split_ifs
  · rw [finrank_gradedPiece_map]
  · rfl
end GroundTheory.Heights₂.Heights.FieldNumbers
