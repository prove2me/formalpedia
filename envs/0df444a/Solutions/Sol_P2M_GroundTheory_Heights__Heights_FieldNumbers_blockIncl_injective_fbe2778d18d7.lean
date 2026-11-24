-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_blockIncl_injective_fbe2778d18d7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:50.952662+00:00
-- url     : https://prove2.me/submissions/781288fc-4a0e-411d-8b77-43a6a3e15f0a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples

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
theorem _root_.solution {K K' : Type*} (j : K ↪ K') (ι' : K' → Type*) :
    Function.Injective (blockIncl j ι') := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  simp only [blockIncl, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  cases j.injective h1
  rw [eq_of_heq h2]
end GroundTheory.Heights₂.Heights.FieldNumbers
