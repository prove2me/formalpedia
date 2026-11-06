-- Prove2me | solution 2 for QEC.Semantics.Davies.actualFrequency_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:05:10.822735+00:00
-- url     : https://prove2.me/submissions/c0f90a92-0156-4b15-bf2e-d5b3b96d19ad

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
namespace QEC.Semantics.Davies
theorem _root_.solution (H A B : Operator V) (hH : H.IsSymmetric) (ω : ℝ) :
    actualFrequency H hH (A+B) ω = actualFrequency H hH A ω + actualFrequency H hH B ω :=
  frequencyComponent_add _ _ _ _ _
end QEC.Semantics.Davies
