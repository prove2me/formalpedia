-- Prove2me | solution 1 for ThreeSum.KaratsubaInterface.le_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:31:45.726407+00:00
-- url     : https://prove2.me/submissions/556482b0-faf2-4a80-bd3c-40f560bdc42a

import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface

set_option autoImplicit false
open ThreeSum ThreeSum.KaratsubaInterface
open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial
namespace ThreeSum.KaratsubaInterface
theorem _root_.solution (p : ℕ) : p ≤ capacity p := Nat.le_pow_clog (by decide) p
end ThreeSum.KaratsubaInterface
