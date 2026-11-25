-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.coeff_single_zero_F_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:32:14.331086+00:00
-- url     : https://prove2.me/submissions/c041e31f-1f03-4f5e-95f0-bebb7c9cd565

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_formalGroupLaw_ev_x_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_zero_right


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
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution {K : Type} [CommRing K] {d : ℕ} (G : FGLaw K d) (c i : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1) (G.F c) = if c = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), i) 1)) (formalGroupLaw_ev_x_zero G c)
  rw [coeff_ev_zero_right, Finsupp.embDomain_single] at h
  rw [show (eXv d) ((0 : Fin 1), i) = ((0 : Fin 2), i) from rfl] at h
  rw [h, coeff_X]
  by_cases hci : c = i
  · subst hci; simp
  · rw [if_neg, if_neg hci]
    intro he
    exact hci (congrArg Prod.snd (Finsupp.single_left_injective one_ne_zero he)).symm
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
