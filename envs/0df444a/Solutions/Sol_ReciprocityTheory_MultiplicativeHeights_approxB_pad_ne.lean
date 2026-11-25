-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_pad_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:09.318771+00:00
-- url     : https://prove2.me/submissions/49df6c5b-bd3a-4bb7-b1ea-5809a7c68e78

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (hx : x ≠ 0) : approxPadPos x ≠ 0 := by
  intro h
  apply hx
  funext k
  have h1 := congr_fun h k.1
  simpa [approxPadPos, k.2] using h1
end ReciprocityTheory.MultiplicativeHeights
