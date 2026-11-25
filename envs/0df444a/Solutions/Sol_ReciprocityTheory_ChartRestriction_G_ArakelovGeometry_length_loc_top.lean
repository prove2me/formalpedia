-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.length_loc_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:30.440059+00:00
-- url     : https://prove2.me/submissions/b167a8b8-e3b8-45af-a785-fd07b3ed2868

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_length_loc_quot_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ (⊤ : Ideal R))) = 0 := by
  apply length_loc_quot_eq_zero
  intro h
  exact ‹P.IsPrime›.ne_top (top_le_iff.mp h)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
