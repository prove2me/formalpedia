-- Prove2me | solution 1 for QuantumParallelRepetition.FiniteEventLaw.allWinMass_le_partial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/355867a7-7ccb-484f-8eb7-1f13cadd9ceb

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_FiniteEventLaw_winEvent_antitone

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.FiniteEventLaw
variable {Ω ι : Type*} [Fintype Ω]
namespace QuantumParallelRepetition.FiniteEventLaw
theorem _root_.solution [Fintype ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (D : Finset ι) :
    law.eventMass (winEvent wins Finset.univ) ≤
      law.eventMass (winEvent wins D) := by
  apply law.eventMass_mono
  exact winEvent_antitone wins (Finset.subset_univ D)
end QuantumParallelRepetition.FiniteEventLaw
