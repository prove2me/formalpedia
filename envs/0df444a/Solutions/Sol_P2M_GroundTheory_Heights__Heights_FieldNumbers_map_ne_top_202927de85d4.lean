-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_map_ne_top_202927de85d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:54.084738+00:00
-- url     : https://prove2.me/submissions/395b3a0c-ec1a-471e-910a-78403e0a6e87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_map_mem_a8a861175ce6

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
variable {σ : Type*} {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {I : Ideal (MvPolynomial σ F)} (hI : I ≠ ⊤) :
    I.map (map (algebraMap F F')) ≠ ⊤ := by
  intro h
  apply hI
  rw [Ideal.eq_top_iff_one]
  apply mem_of_map_mem (F' := F')
  rw [map_one, h]
  exact Submodule.mem_top
end GroundTheory.Heights₂.Heights.FieldNumbers
