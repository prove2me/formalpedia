-- Prove2me | solution 1 for ThreeSum.BlockIndex.indexSet_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:45.56377+00:00
-- url     : https://prove2.me/submissions/691cc8c3-b1ab-40e4-bbd2-7359d8358771

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_Submission_ThreeSum_BlockIndex

set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndex
open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace ThreeSum.BlockIndex
theorem _root_.solution (J L : ℕ) : Function.Injective (@indexSet J L) :=
  Finset.map_injective _
end ThreeSum.BlockIndex
