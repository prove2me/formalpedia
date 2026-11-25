-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_zero_84a12a66bfd1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:15:01.598967+00:00
-- url     : https://prove2.me/submissions/d8c5e360-b27a-4ffc-b22d-f23a992e3ffe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {K : Type*} {κ : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution {I W : Ideal (NumbersDVR.MRing κ R)} (f : NumbersDVR.MRing κ R)
    (h : ¬ (W.IsPrime ∧ NumbersDVR.IsRelevant W ∧ I ≤ W)) : NumbersDVR.divCycle I f W = 0 := by
  unfold NumbersDVR.divCycle
  rw [dif_neg]
  rintro ⟨hmin, hrel⟩
  exact h ⟨hmin.1.1, hrel, le_sup_left.trans hmin.1.2⟩
end GroundTheory.Heights₂.Heights.SectionCycle
