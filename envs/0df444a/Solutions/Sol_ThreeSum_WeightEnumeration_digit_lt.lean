-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.digit_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:47:17.397043+00:00
-- url     : https://prove2.me/submissions/9631980f-3da7-46ba-a17d-11be29347e0f

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]
namespace ThreeSum.WeightEnumeration
theorem _root_.solution {p width k coordinate : ℕ} (hp : 0 < p) : digit p width k coordinate < p :=
  Nat.mod_lt _ hp
end ThreeSum.WeightEnumeration
