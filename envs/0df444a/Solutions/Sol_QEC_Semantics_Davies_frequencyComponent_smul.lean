-- Prove2me | solution 1 for QEC.Semantics.Davies.frequencyComponent_smul
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:33:17.020681+00:00
-- url     : https://prove2.me/submissions/b6abfc5c-2fe3-48dd-bf21-0126ebfe6fe2

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Theorems.Thm_QEC_Semantics_Davies_entry_ext
import Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem solution (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (c : ℂ) (A : Operator V) (ω : ℝ) :
    frequencyComponent b e (c • A) ω = c • frequencyComponent b e A ω := by
  apply entry_ext b
  intro i j
  simp only [entry_frequencyComponent, entry_smul]
  split_ifs <;> simp
