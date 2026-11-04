-- Prove2me | solution 1 for ThreeSum.Auxiliary.moduli_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:59.582652+00:00
-- url     : https://prove2.me/submissions/9d3e7ffc-45ba-4758-98d2-361e10991548

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary

set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators
namespace ThreeSum.Auxiliary
theorem _root_.solution (C : Finset ℕ) : (moduli C).card = C.card := by
  exact card_image_of_injective C (show Function.Injective (fun p : ℕ => (p : ℤ)) from Nat.cast_injective)
end ThreeSum.Auxiliary
