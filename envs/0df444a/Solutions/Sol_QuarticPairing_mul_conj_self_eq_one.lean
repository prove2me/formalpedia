-- Prove2me | solution 1 for QuarticPairing.mul_conj_self_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:14.518627+00:00
-- url     : https://prove2.me/submissions/f646b58d-da68-4761-9e5f-639cd9901d18

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution {z : ℂ} (hz : ‖z‖ = 1) : z * starRingEnd ℂ z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
end QuarticPairing
