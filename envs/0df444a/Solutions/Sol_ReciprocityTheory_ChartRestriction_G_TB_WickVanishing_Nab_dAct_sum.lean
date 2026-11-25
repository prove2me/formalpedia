-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.dAct_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:10.144156+00:00
-- url     : https://prove2.me/submissions/74e514a9-fb64-425c-b70d-067a2de77a7d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_coeff_act_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (B : FB R d O) (w0 : O) (hw : w0 + star w0 = 1) (i j : Fin d) :
    dAct k B w0 i j + dAct k B (star w0) i j = if i = j then 1 else 0 := by
  simp only [dAct, FB.actK, MvPowerSeries.coeff_map]
  rw [← map_add, ← coeff_act_add, hw, B.A.one_act]
  simp only [pt, MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · have h' : Finsupp.single ((0 : Fin 1), j) 1 ≠ Finsupp.single ((0 : Fin 1), i) 1 := by
      intro e
      rw [Finsupp.single_left_inj one_ne_zero] at e
      exact h (Prod.mk.inj e).2.symm
    simp [h, h']
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
