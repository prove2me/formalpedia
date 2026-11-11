-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.dissipator_selfAdjointTraceNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:45:10.769198+00:00
-- url     : https://prove2.me/submissions/f6c28322-8e2e-40bc-bd06-bba97c54e076

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_coupling_operatorNorm_le_one
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_couplingIndex_card
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_symmetric
import Theorems.Thm_QEC_Semantics_Davies_hamiltonianDissipator_selfAdjointTraceNorm_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ) (hmax : ℝ)
    (hm : 0 ≤ hmax) (hn : ∀ qa ω, 0 ≤ rate qa ω) (hu : ∀ qa ω, rate qa ω ≤ hmax) :
    selfAdjointTraceNormOneToOne (dissipator S n rate) ≤
      6 * Fintype.card (Physical S n) * hmax := by
  have h := hamiltonianDissipator_selfAdjointTraceNorm_le
    (BDL26CSSHamiltonian.hamiltonian S n) (hamiltonian_symmetric S n)
    (fun qa : CouplingIndex S n => coupling S n qa.1 qa.2)
    (fun qa => coupling_operatorNorm_le_one S n qa.1 qa.2) rate hmax hm hn hu
  calc
    _ ≤ 2 * (Fintype.card (CouplingIndex S n) : ℝ) * hmax := h
    _ = 6 * Fintype.card (Physical S n) * hmax := by
      rw [couplingIndex_card]
      push_cast
      ring
end QEC.Coding.BDL26BoundedRateDavies
