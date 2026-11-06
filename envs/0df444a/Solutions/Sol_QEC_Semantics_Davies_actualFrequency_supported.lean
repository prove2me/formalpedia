-- Prove2me | solution 1 for QEC.Semantics.Davies.actualFrequency_supported
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:40:48.309567+00:00
-- url     : https://prove2.me/submissions/4c1e0d25-9f60-45ea-997c-101b59a650a1

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Theorems.Thm_QEC_Semantics_Davies_hamiltonian_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyFilter_eq_component
import Theorems.Thm_QEC_Semantics_Davies_frequencyFilter_supported
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_of_not_mem
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_zero
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {q : Type} [Fintype q] [DecidableEq q]

theorem solution (S : FiniteSubsystem q)
    (H A : Operator (Qubit.QubitRegister q)) (hH : H.IsSymmetric)
    (hsH : S.OperatorSupportedOnRegister H) (hsA : S.OperatorSupportedOnRegister A) (ω : ℝ) :
    S.OperatorSupportedOnRegister (actualFrequency H hH A ω) := by
  let b := hamiltonianBasis H hH
  let e := hamiltonianEnergies H hH
  by_cases hw : ω ∈ frequencies e
  · have he := frequencyFilter_eq_component b e ω hw A
    rw [hamiltonian_diagonal] at he
    rw [actualFrequency, ← he]
    exact frequencyFilter_supported S H A ω _ hsH hsA
  · have he := frequencyComponent_of_not_mem b e A ω hw
    change S.OperatorSupportedOnRegister (frequencyComponent b e A ω)
    rw [he]
    exact FiniteSubsystem.supported_zero S
