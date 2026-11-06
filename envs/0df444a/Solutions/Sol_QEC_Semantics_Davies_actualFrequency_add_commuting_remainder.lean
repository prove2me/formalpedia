-- Prove2me | solution 1 for QEC.Semantics.Davies.actualFrequency_add_commuting_remainder
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:41:07.180294+00:00
-- url     : https://prove2.me/submissions/2616b4a4-d2c7-4cba-a0ec-a2e278bb4789

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Theorems.Thm_QEC_Semantics_Davies_hamiltonian_diagonal
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_mul_left
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_mul_right
import Theorems.Thm_QEC_Semantics_Davies_actualFrequency_energyDifference
import Theorems.Thm_QEC_Semantics_Davies_sum_frequencyComponent
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_sum
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_of_eigenoperator
import Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_of_not_mem
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem solution (L R A : Operator V)
    (hL : L.IsSymmetric) (hH : (L+R).IsSymmetric)
    (hLR : Commute L R) (hRA : Commute R A) (ω : ℝ) :
    actualFrequency (L+R) hH A ω = actualFrequency L hL A ω := by
  let b := hamiltonianBasis L hL
  let e := hamiltonianEnergies L hL
  have hR : Commute (diagonal b e) R := by simpa [b,e,hamiltonian_diagonal] using hLR
  have hc : ∀ freq, Commute R (frequencyComponent b e A freq) := by
    intro freq
    have h := congrArg (fun B => frequencyComponent b e B freq) hRA.eq
    rw [frequencyComponent_mul_left b e R A hR,
      frequencyComponent_mul_right b e A R hR] at h
    exact h
  have heig : ∀ freq, energyDifference (L+R) (frequencyComponent b e A freq) =
      (freq : ℂ) • frequencyComponent b e A freq := by
    intro freq
    have h := actualFrequency_energyDifference L hL A freq
    change energyDifference L (frequencyComponent b e A freq) = _ at h
    simp only [energyDifference, mul_add, add_mul] at h ⊢
    rw [(hc freq).eq]
    convert h using 1 <;> abel
  have hsum := sum_frequencyComponent b e A
  unfold actualFrequency
  conv_lhs => rw [← hsum]
  rw [frequencyComponent_sum]
  have hselect : ∀ freq,
      frequencyComponent (hamiltonianBasis (L+R) hH) (hamiltonianEnergies (L+R) hH)
        (frequencyComponent b e A freq) ω =
        if freq=ω then frequencyComponent b e A freq else 0 := by
    intro freq
    apply frequencyComponent_of_eigenoperator
    simpa only [hamiltonian_diagonal] using heig freq
  simp_rw [hselect]
  by_cases hw : ω ∈ frequencies e
  · let w : Frequency e := ⟨ω,hw⟩
    rw [Finset.sum_eq_single w]
    · simp [w,b,e]
    · intro k _ hk
      have hn : k.val ≠ ω := fun h => hk (Subtype.ext h)
      simp [hn]
    · simp
  · rw [frequencyComponent_of_not_mem b e A ω hw]
    apply Finset.sum_eq_zero
    intro k _
    have hn : k.val ≠ ω := fun h => hw (h ▸ k.property)
    simp [hn]
