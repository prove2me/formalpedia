-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_map_mem_a8a861175ce6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:37.357855+00:00
-- url     : https://prove2.me/submissions/12b605de-ecb9-4a69-949d-e27a6581c7e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_map_b399740e1b2a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeffForm_mem_0f251d0f8cfe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_one_413d684437fd

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
theorem _root_.solution {I : Ideal (MvPolynomial σ F)} {g : MvPolynomial σ F}
    (h : map (algebraMap F F') g ∈ I.map (map (algebraMap F F'))) : g ∈ I := by
  obtain ⟨φ, hφ⟩ := exists_form_one (F := F) (F' := F')
  have := coeffForm_mem φ h
  rwa [coeffForm_map φ hφ] at this
end GroundTheory.Heights₂.Heights.FieldNumbers
