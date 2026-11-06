-- Prove2me | solution 1 for QEC.Semantics.Davies.actualFrequency_add
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:33:18.122826+00:00
-- url     : https://prove2.me/submissions/bbbe6769-cee2-4d60-aff9-71cf2339f822

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_add
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem solution (H A B : Operator V) (hH : H.IsSymmetric) (ω : ℝ) :
    actualFrequency H hH (A+B) ω = actualFrequency H hH A ω + actualFrequency H hH B ω :=
  frequencyComponent_add _ _ _ _ _
