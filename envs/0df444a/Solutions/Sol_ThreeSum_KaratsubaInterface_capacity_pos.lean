-- Prove2me | solution 1 for ThreeSum.KaratsubaInterface.capacity_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:31:42.40111+00:00
-- url     : https://prove2.me/submissions/bd90c903-b2fc-46ce-a484-fcbf04967f6f

import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface

set_option autoImplicit false
open ThreeSum ThreeSum.KaratsubaInterface
open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial
namespace ThreeSum.KaratsubaInterface
theorem _root_.solution (p : ℕ) : 0 < capacity p := Nat.pow_pos (by decide)
end ThreeSum.KaratsubaInterface
