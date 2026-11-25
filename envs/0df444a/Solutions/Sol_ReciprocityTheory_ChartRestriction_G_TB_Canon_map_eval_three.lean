-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.Canon.map_eval_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:38.003152+00:00
-- url     : https://prove2.me/submissions/0bf8d586-ad0a-4a32-9d82-a8bfb7a6c6d2

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
theorem _root_.solution (f : PS R 3 d) (u v w : Q R d n) :
    MvPowerSeries.map φ (E3 f u v w) = E3 (MvPowerSeries.map φ f) (mq φ u) (mq φ v) (mq φ w) := by
  unfold E3
  have h : (fun j => mq φ (![u, v, w] j)) = ![mq φ u, mq φ v, mq φ w] := by
    funext j; fin_cases j <;> rfl
  rw [map_sb, h]
end ReciprocityTheory.ChartRestriction.G.TB.Canon
