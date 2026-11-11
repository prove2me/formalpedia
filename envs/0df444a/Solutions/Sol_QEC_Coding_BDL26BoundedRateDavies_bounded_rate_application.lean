-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.bounded_rate_application
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:56:40.303356+00:00
-- url     : https://prove2.me/submissions/f6bf4230-0232-4005-bd78-fd1190095849

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_gibbs_stationary
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_dissipator_selfAdjointTraceNorm_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution
    (rate : CouplingIndex S n → BDL26CSSDaviesLocality.Frequency S n → ℝ)
    (β hmax : ℝ) (_hβ : 0 ≤ β) (hm : 0 < hmax)
    (hr : ∀ qa ω, 0 < rate qa ω ∧ rate qa ω ≤ hmax)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S n ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S n rate (BDL26CSSHamiltonian.gibbs S n β).toOperator = 0 ∧
      selfAdjointTraceNormOneToOne (dissipator S n rate) ≤
        6 * Fintype.card (Physical S n) * hmax :=
  ⟨gibbs_stationary S n rate β (fun qa ω => (hr qa ω).1.le) hDB,
    dissipator_selfAdjointTraceNorm_le S n rate hmax hm.le
      (fun qa ω => (hr qa ω).1.le) (fun qa ω => (hr qa ω).2)⟩
end QEC.Coding.BDL26BoundedRateDavies
