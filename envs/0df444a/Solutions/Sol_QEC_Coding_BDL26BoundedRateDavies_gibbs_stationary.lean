-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.gibbs_stationary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:47:09.075415+00:00
-- url     : https://prove2.me/submissions/42817ba9-41ef-4aed-a1a3-bd2ef9c1d00d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_coupling_symmetric
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_actual_gibbs_eq
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric
import Theorems.Thm_QEC_Semantics_Davies_hamiltonianGibbs_stationary


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) (β : ℝ)
    (hn : ∀ qa ω, 0 ≤ rate qa ω)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S n ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S n rate (BDL26CSSHamiltonian.gibbs S n β).toOperator = 0 := by
  rw [actual_gibbs_eq]
  exact hamiltonianGibbs_stationary (BDL26CSSHamiltonian.hamiltonian S n)
    (hamiltonian_symmetric S n) (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2)
    (fun qa => coupling_symmetric S n qa.1 qa.2) rate β hn hDB
end QEC.Coding.BDL26BoundedRateDavies
