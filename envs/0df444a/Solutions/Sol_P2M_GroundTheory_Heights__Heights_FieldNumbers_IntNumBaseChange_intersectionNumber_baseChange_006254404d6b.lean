-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumBaseChange_intersectionNumber_baseChange_006254404d6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:26:59.162872+00:00
-- url     : https://prove2.me/submissions/1e18d751-2908-4508-9e0f-30ebb2def4b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomogIdeal_map_e1ed5f7bf88c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isRelevant_map_c55c7df7a8e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_hilbFn_map_ba3c10076c2a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isPrime_map_ratFunc_3552ddc99f6c

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace IntNumBaseChange
theorem _root_.solution : IntNumBaseChange.Statement := by
  refine ⟨?_, ?_⟩
  · intro F _ F' _ _ K _ _ ι _ I
    have h : ∀ m, hilbFn (I.map (MvPolynomial.map (algebraMap F F'))) m = hilbFn I m :=
      hilbFn_map I
    refine ⟨h, fun n bs => ?_⟩
    unfold intNum
    rw [show hilbFn (I.map (MvPolynomial.map (algebraMap F F'))) = hilbFn I from funext h]
  · intro F _ K _ _ ι _ P hP
    have := hP.isPrime
    exact ⟨isPrime_map_ratFunc P, isMultiHomogIdeal_map hP.multiHomog,
      isRelevant_map hP.relevant⟩
end IntNumBaseChange
end GroundTheory.Heights₂.Heights.FieldNumbers
