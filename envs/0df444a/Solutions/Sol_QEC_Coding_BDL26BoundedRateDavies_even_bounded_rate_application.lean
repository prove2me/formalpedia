-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.even_bounded_rate_application
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:25:22.678486+00:00
-- url     : https://prove2.me/submissions/3e9f76ac-0e3c-4c45-aca0-c4fa7f532add

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_bounded_rate_application

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution (k : Nat)
    (rate : CouplingIndex S (2*k) → BDL26CSSDaviesLocality.Frequency S (2*k) → ℝ)
    (β hmax : ℝ) (hβ : 0 ≤ β) (hm : 0 < hmax)
    (hr : ∀ qa ω, 0 < rate qa ω ∧ rate qa ω ≤ hmax)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S (2*k) ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S (2*k) rate (BDL26CSSHamiltonian.gibbs S (2*k) β).toOperator = 0 ∧
      selfAdjointTraceNormOneToOne (dissipator S (2*k) rate) ≤
        6 * Fintype.card (Physical S (2*k)) * hmax :=
  bounded_rate_application S (2*k) rate β hmax hβ hm hr hDB
end QEC.Coding.BDL26BoundedRateDavies
