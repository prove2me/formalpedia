-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCanonicalTupleCodes.digit_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:12:49.255082+00:00
-- url     : https://prove2.me/submissions/4420cde2-f795-4752-a0c5-856100685f4f

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleWantedLookup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Theorems.Thm_ThreeSum_WeightedGlobalNativeTupleWitness_positional_cast_digits
import Theorems.Thm_ThreeSum_WeightedGlobalNativeTupleWitness_positional_map


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCanonicalTupleCodes
open TernaryJointType
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalCanonicalTupleCodes
theorem _root_.solution (R : ℕ) {A : Type*} (raw : A→ℕ) (xs : List A) :
    Radix.positionalHash (R : ℤ) (fun a => (raw a : ℤ)) xs=
      ((Nat.ofDigits R (xs.map raw) : ℕ) : ℤ) := by
  calc
    _ = Radix.positionalHash (R : ℤ) (fun a : ℕ => (a : ℤ)) (xs.map raw) :=
      WeightedGlobalNativeTupleWitness.positional_map (R : ℤ) raw (fun a : ℕ => (a : ℤ)) xs
    _ = _ := WeightedGlobalNativeTupleWitness.positional_cast_digits R (xs.map raw)
end ThreeSum.WeightedGlobalCanonicalTupleCodes
