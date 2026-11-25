-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.colM_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:15:35.705844+00:00
-- url     : https://prove2.me/submissions/b31af775-40ce-4bb3-91fc-33e815204a99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_glue_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (g : Fin n → (ι →₀ ℕ)) (b : Fin n) : colM (glue g) b = g b := by
  ext l
  first
  | simp [colM, glue_apply]
  | exact glue_apply g l b
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
