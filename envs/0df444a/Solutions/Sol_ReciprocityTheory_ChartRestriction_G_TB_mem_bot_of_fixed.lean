-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.mem_bot_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:33:42.933185+00:00
-- url     : https://prove2.me/submissions/29709a23-fd31-44dd-a14d-2fcce1cb25fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JInjCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution {K F : Type} [Field K] [Field F] [Algebra K F] [IsGalois K F] (a : F)
    (ha : ∀ g : F ≃ₐ[K] F, g a = a) : a ∈ (⊥ : IntermediateField K F) := by
  exact (InfiniteGalois.mem_bot_iff_fixed a).mpr ha
end ReciprocityTheory.ChartRestriction.G.TB
