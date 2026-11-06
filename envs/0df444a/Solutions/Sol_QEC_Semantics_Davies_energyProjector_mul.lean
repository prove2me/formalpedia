-- Prove2me | solution 1 for QEC.Semantics.Davies.energyProjector_mul
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:33:14.605967+00:00
-- url     : https://prove2.me/submissions/de0e0f51-c773-4d8a-86b6-fe99baec6dd5

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Theorems.Thm_QEC_Semantics_Davies_entry_ext
import Theorems.Thm_QEC_Semantics_Davies_entry_mul
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) (E F : ℝ) :
    energyProjector b energy E * energyProjector b energy F =
      if E = F then energyProjector b energy E else 0 := by
  apply entry_ext b
  intro i j
  rw [entry_mul]
  simp only [entry_energyProjector, entry_ite, entry_zero, ite_and]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst j; split_ifs <;> simp_all
  · simp [hij]
