-- Prove2me | solution 1 for QEC.Semantics.Davies.frequencyFilter_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:13:04.758239+00:00
-- url     : https://prove2.me/submissions/d3b25a7f-0af1-4e91-85b9-f993bfd495be

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_mul
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_smul
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_sub


set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {q : Type} [Fintype q] [DecidableEq q]
namespace QEC.Semantics.Davies
theorem _root_.solution (S : FiniteSubsystem q)
    (H A : Operator (Qubit.QubitRegister q)) (ω : ℝ) (l : List ℝ)
    (hH : S.OperatorSupportedOnRegister H) (hA : S.OperatorSupportedOnRegister A) :
    S.OperatorSupportedOnRegister (frequencyFilter H ω l A) := by
  induction l with
  | nil => exact hA
  | cons ν l ih =>
    exact S.supported_smul _ (S.supported_sub
      (S.supported_sub (S.supported_mul ih hH) (S.supported_mul hH ih))
      (S.supported_smul _ ih))
end QEC.Semantics.Davies
