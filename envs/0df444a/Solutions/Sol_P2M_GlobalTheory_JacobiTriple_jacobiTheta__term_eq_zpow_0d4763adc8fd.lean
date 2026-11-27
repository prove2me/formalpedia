-- Prove2me | solution 1 for P2M_GlobalTheory_JacobiTriple_jacobiTheta__term_eq_zpow_0d4763adc8fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:33:51.072817+00:00
-- url     : https://prove2.me/submissions/c26ca4d3-e21e-43b6-a209-a8d8b1956233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.JacobiTriple
namespace GlobalTheory.JacobiTriple
theorem _root_.solution (τ z : ℂ) (j : ℤ) :
    jacobiTheta₂_term j z τ = cexp (2 * π * I * z) ^ j * cexp (π * I * τ) ^ (j ^ 2) := by
  unfold jacobiTheta₂_term
  rw [← exp_int_mul, ← exp_int_mul, ← exp_add]
  congr 1
  push_cast
  ring
end GlobalTheory.JacobiTriple
