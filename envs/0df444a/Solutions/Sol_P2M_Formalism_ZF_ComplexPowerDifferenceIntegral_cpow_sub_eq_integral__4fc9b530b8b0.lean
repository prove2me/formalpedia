-- Prove2me | solution 1 for P2M_Formalism_ZF_ComplexPowerDifferenceIntegral_cpow_sub_eq_integral__4fc9b530b8b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:48:30.835113+00:00
-- url     : https://prove2.me/submissions/6a56dcb2-0b44-4d1d-a824-ea5aa074bdd9

import Mathlib
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormCpowSubLePoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.ComplexPowerDifferenceIntegral
namespace Formalism.ZF.ComplexPowerDifferenceIntegral
theorem _root_.solution {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {s : ℂ} (hs : s ≠ 0) :
    (x : ℂ) ^ (-s) - (y : ℂ) ^ (-s) = s * ∫ t in x..y, (t : ℂ) ^ (-s - 1) := by
  have h0 : (0:ℝ) ∉ Set.uIcc x y := by
    rw [Set.uIcc_of_le hxy]; intro h; exact absurd h.1 (not_le.mpr hx)
  have hr : (-s - 1) ≠ -1 := by intro h; apply hs; linear_combination -h
  have hs' : -s ≠ 0 := neg_ne_zero.mpr hs
  rw [integral_cpow (Or.inr ⟨hr, h0⟩)]
  have e : -s - 1 + 1 = -s := by ring
  rw [e, mul_div_assoc', eq_div_iff hs']
  ring
end Formalism.ZF.ComplexPowerDifferenceIntegral
