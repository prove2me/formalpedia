-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_X_709b97b21fde
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:49:27.92538+00:00
-- url     : https://prove2.me/submissions/f7ea7e97-0fa4-4ecf-a579-ebc57af02b62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]


theorem solution {J : Type} (v : Σ k, ι k) :
    liftForm (J := J) (X v : MRing ι R) = X ⟨some v.1, v.2⟩ := by
  first | rfl | simp [liftForm]
