-- Prove2me | solution 1 for QEC.Semantics.Davies.actualFrequency_zeroHamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:33:19.3422+00:00
-- url     : https://prove2.me/submissions/3f426f56-4287-47d8-82c9-3d4c023866dc

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Theorems.Thm_QEC_Semantics_Davies_actualFrequency_of_eigenoperator
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem solution (A : Operator V) (ω : ℝ) :
    actualFrequency 0 LinearMap.IsSymmetric.zero A ω = if 0=ω then A else 0 := by
  apply actualFrequency_of_eigenoperator
  simp [energyDifference]
