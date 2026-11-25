-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.mq_ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:52:22.318117+00:00
-- url     : https://prove2.me/submissions/2b6791c9-b31e-4f55-a458-aa62c4cd380a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_map_sb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d n l : ℕ}
variable [Algebra ℚ k]
omit [Algebra ℚ k]
variable {R : Type} [CommRing R] (φ : R →+* k)
namespace ReciprocityTheory.ChartRestriction.G.TB.Canon
theorem _root_.solution (A : Q R d 1) (u : Q R d n) : mq φ (ac A u) = ac (mq φ A) (mq φ u) := by
  apply Subtype.ext; funext i
  show MvPowerSeries.map φ (sb ![u] (A.1 i)) = sb ![mq φ u] (MvPowerSeries.map φ (A.1 i))
  have h : (fun j => mq φ (![u] j)) = ![mq φ u] := by
    funext j; fin_cases j; rfl
  rw [map_sb, h]
end ReciprocityTheory.ChartRestriction.G.TB.Canon
