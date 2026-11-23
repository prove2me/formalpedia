-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.formalSeriesValueAtThreePoints_genericPoints
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:30.090822+00:00
-- url     : https://prove2.me/submissions/6482745a-c45e-4cf3-9140-bf916a548d07

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_sb_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution (f : PS k 3 d) : E3 f (gen 0) (gen 1) (gen 2) = f := by
  have h : (![gen 0, gen 1, gen 2] : Fin 3 → Q k d 3) = gen := by
    funext i
    fin_cases i <;> rfl
  show sb ![gen 0, gen 1, gen 2] f = f
  rw [h, sb_gen]
end ReciprocityTheory.ChartRestriction.G.TB.Canon
