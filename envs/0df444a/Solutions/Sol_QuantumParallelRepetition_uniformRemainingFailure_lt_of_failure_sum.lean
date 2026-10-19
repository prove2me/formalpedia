-- Prove2me | solution 1 for QuantumParallelRepetition.uniformRemainingFailure_lt_of_failure_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/6d1cdbfb-270f-4485-90e8-715e6483391e

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
namespace QuantumParallelRepetition
theorem _root_.solution
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) {η : ℝ}
    (hp : 0 < postselectionMass law wins C)
    (hm : 0 < (Finset.univ \ C).card)
    (hfailure :
      (∑ i ∈ Finset.univ \ C,
        FiniteEventLaw.failureMass law wins C i) <
        ((Finset.univ \ C).card : ℝ) *
          (η * postselectionMass law wins C)) :
    uniformRemainingFailure law wins C < η := by
  have hmreal : 0 < ((Finset.univ \ C).card : ℝ) := by
    exact_mod_cast hm
  unfold uniformRemainingFailure conditionalCoordinateFailure
  rw [← Finset.sum_div]
  apply (div_lt_iff₀ hmreal).mpr
  apply (div_lt_iff₀ hp).mpr
  nlinarith
end QuantumParallelRepetition
