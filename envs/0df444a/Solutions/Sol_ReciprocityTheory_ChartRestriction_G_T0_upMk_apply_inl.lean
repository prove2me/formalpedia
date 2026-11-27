-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.upMk_apply_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:29:17.638413+00:00
-- url     : https://prove2.me/submissions/3cdda4eb-892a-4b47-9f81-bdc32fe873a6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {D N : ℕ} (ab : (Fin (D + 2) →₀ ℕ) × (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ))
    (p : Fin (D + 2) × Fin (N + 1)) : upMk ab (Sum.inl p) = ab.2 (some p) := rfl
end ReciprocityTheory.ChartRestriction.G.T0
