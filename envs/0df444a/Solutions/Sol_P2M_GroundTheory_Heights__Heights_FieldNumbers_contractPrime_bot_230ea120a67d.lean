-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_contractPrime_bot_230ea120a67d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:04.512751+00:00
-- url     : https://prove2.me/submissions/bde40025-ff3d-4ae0-9e0d-6985dda2c44c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_blockIncl_injective_fbe2778d18d7

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
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {K K' : Type*} {F : Type*} [Field F] (j : K ↪ K') (ι' : K' → Type*) :
    contractPrime j (⊥ : Ideal (MRing ι' F)) = ⊥ :=
  Ideal.comap_bot_of_injective _ (rename_injective _ (blockIncl_injective j ι'))
end GroundTheory.Heights₂.Heights.FieldNumbers
