-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:30.460412+00:00
-- url     : https://prove2.me/submissions/d9ae6f9c-af61-4c5c-8f05-8c9ff168320b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_rename_component_5131e4e3c8a4

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
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
variable [DecidableEq K] [DecidableEq K']
variable {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {P' : Ideal (MRing ι' F)} (hP' : IsMultiProjPrime P') :
    IsMultiProjPrime (contractPrime j P') where
  isPrime := by
    have := hP'.isPrime
    exact contractPrime.isPrime j P'
  multiHomog := by
    intro f hf b
    show rename (blockIncl j ι') _ ∈ P'
    rw [rename_component]
    exact hP'.multiHomog _ hf _
  relevant := by
    intro k
    obtain ⟨i, hi⟩ := hP'.relevant (j k)
    refine ⟨i, ?_⟩
    show rename (blockIncl j ι') (X ⟨k, i⟩) ∉ P'
    rw [rename_X]
    exact hi
end GroundTheory.Heights₂.Heights.FieldNumbers
