-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val.harmonic_value_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:44:17.766926+00:00
-- url     : https://prove2.me/submissions/edbad4ab-9dba-43ac-986c-9e8cb22bf395

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionSecondOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_const_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_bE_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_E_liftX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Val_E_nablaPoly

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.TB.ValueSt := by
  intro R _ d O _ _ k _ _ _ B h hax m ι _ u P g
  rw [← const_subst (bE_const k h hax) (nablaPoly k B h m u P (liftX k g)), E_nablaPoly B h hax m u P,
    E_liftX k h hax g]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
