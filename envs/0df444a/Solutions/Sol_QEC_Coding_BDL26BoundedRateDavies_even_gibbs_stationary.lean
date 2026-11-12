-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedRateDavies.even_gibbs_stationary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:24:20.556059+00:00
-- url     : https://prove2.me/submissions/5f9e58b2-5240-4cd1-9788-702955b765d0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Theorems.Thm_QEC_Coding_BDL26BoundedRateDavies_gibbs_stationary

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BoundedRateDavies
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26CSSDaviesLocality
open Semantics Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26BoundedRateDavies
theorem _root_.solution (k : Nat)
    (rate : CouplingIndex S (2*k) → BDL26CSSDaviesLocality.Frequency S (2*k) → ℝ) (β : ℝ)
    (hn : ∀ qa ω, 0 ≤ rate qa ω)
    (hDB : ∀ qa ω, rate qa (oppositeFrequency S (2*k) ω) =
      Real.exp (-β * ω.val) * rate qa ω) :
    dissipator S (2*k) rate (BDL26CSSHamiltonian.gibbs S (2*k) β).toOperator = 0 :=
  gibbs_stationary S (2*k) rate β hn hDB
end QEC.Coding.BDL26BoundedRateDavies
