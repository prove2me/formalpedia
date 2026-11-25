-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_map_e1ed5f7bf88c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:26.882818+00:00
-- url     : https://prove2.me/submissions/1d1e6b32-9908-4233-928d-f6712a2ccb07

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_weightedHomogeneousComponent_fab16ab76a0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_mem_0f251d0f8cfe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_map_of_coeffForm_538bf3f530b9

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
variable {K : Type*} {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution [DecidableEq K] {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    IsMultiHomogIdeal (I.map (map (algebraMap F F'))) := by
  intro f hf b
  apply mem_map_of_coeffForm
  intro φ
  rw [coeffForm_weightedHomogeneousComponent]
  exact hI _ (coeffForm_mem φ hf) b
end GroundTheory.Heights₂.Heights.FieldNumbers
