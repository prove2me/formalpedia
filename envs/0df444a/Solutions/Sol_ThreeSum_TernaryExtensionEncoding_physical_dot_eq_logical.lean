-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.physical_dot_eq_logical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:37:58.84555+00:00
-- url     : https://prove2.me/submissions/20a9a175-dfcd-4ed9-b682-2191019a8a68

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (J : ℕ) (raw coeff : Fin (J+2) → ZMod p) :
    (∑ i, raw (digitOrder J i)*coeff (digitOrder J i))=∑ i, raw i*coeff i :=
  Equiv.sum_comp (digitOrder J) (fun i => raw i*coeff i)
end ThreeSum.TernaryExtensionEncoding
