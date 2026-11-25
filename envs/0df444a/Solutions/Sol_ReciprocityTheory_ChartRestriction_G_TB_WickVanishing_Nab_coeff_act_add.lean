-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.coeff_act_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:47.157613+00:00
-- url     : https://prove2.me/submissions/b6818a37-70a3-4446-90d6-4df149d2cc99

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_coeff_single_zero_F_eq_ite
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_ev__53681771e208
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_cc_pderiv__e7c46f068b17
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_coeff_F_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d2


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
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
theorem _root_.solution (B : FB R d O) (a b : O) (i j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act (a + b) i) =
      coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act a i) + coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act b i) := by
  rw [B.A.add_act a b]
  show coeff _ (ev (n := 1) ![B.A.act a, B.A.act b] (B.G.F i)) = _
  have hab : CZ (![B.A.act a, B.A.act b] : Fin 2 → Pt R 1 d) := CZ.cons (B.A.const a) (CZ.cons (B.A.const b) CZ.nil)
  rw [← cc_pderiv', ← cc_pderiv' (B.A.act a i), ← cc_pderiv' (B.A.act b i), d2 hab]
  simp only [map_add, map_sum, map_mul, cc_ev' hab, cc_pderiv', coeff_single_zero_F_eq_ite, coeff_F_y, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
