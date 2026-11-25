-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.isIntegralElt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:01:19.730937+00:00
-- url     : https://prove2.me/submissions/e9e33f77-8572-423b-96de-cfeb6d9d0ad7

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {x y : K} (hx : IsIntegralElt x)
    (hy : IsIntegralElt y) : IsIntegralElt (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩
end ReciprocityTheory.MultiplicativeHeights.SemiPt
