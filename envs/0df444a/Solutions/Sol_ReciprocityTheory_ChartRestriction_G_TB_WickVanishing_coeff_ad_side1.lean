-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ad_side1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:54:08.763483+00:00
-- url     : https://prove2.me/submissions/98f72875-8639-45a5-9ceb-c64c3aa9c345

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_subst_xz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_first_point_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_degree_xz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_xz_mul_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_const_actK

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (a : O) (i j : Fin d) :
    coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1)
        (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h) =
      ∑ l, coeff (single ((0 : Fin 2), l) 1 + single ((1 : Fin 2), i) 1) h * dAct k B a l j := by
  classical
  unfold ev
  rw [coeff_subst_xz h hc.ax0 hc.ax1 _ ?_ _ (degree_xz j i)]
  · refine Finset.sum_congr rfl fun l _ => ?_
    have e0 : ![comp1 (B.actK k a) (pt k d 0), pt k d 1] ((0, l) : Fin 2 × Fin d).1 ((0, l) : Fin 2 × Fin d).2 =
        rename (eXv d) (B.actK k a l) := eval_first_point_rename _
    have e1 : ∀ m : Fin d, ![comp1 (B.actK k a) (pt k d 0), pt k d 1] ((1, m) : Fin 2 × Fin d).1
        ((1, m) : Fin 2 × Fin d).2 = X ((1 : Fin 2), m) := fun m => rfl
    simp only [e0, e1, coeff_xz_mul_X, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · rintro ⟨j', i'⟩
    fin_cases j'
    · show constantCoeff (ev (n := 2) ![pt k d 0] (B.actK k a i')) = 0
      rw [eval_first_point_rename, constantCoeff_rename, const_actK]
    · exact constantCoeff_X _
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
