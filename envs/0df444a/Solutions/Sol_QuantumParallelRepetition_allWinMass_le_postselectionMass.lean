-- Prove2me | solution 1 for QuantumParallelRepetition.allWinMass_le_postselectionMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/8e736dac-f7b4-48fc-b05f-9dd8201e51f7

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_FiniteEventLaw_allWinMass_le_partial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
omit [DecidableEq ι]
namespace QuantumParallelRepetition
theorem _root_.solution
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) :
    law.eventMass (FiniteEventLaw.winEvent wins Finset.univ) ≤
      postselectionMass law wins C :=
  law.allWinMass_le_partial wins C
end QuantumParallelRepetition
