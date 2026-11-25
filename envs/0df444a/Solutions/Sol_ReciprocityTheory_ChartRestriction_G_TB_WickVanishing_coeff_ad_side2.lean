-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ad_side2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:23.930791+00:00
-- url     : https://prove2.me/submissions/1e62bc57-05c7-4ab9-b5ab-92ae19a3fc6e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_subst_xz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_second_point_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_degree_xz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_xz_X_mul
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
        (ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) =
      ∑ m, coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), m) 1) h * dAct k B (star a) m i := by
  classical
  unfold ev
  rw [coeff_subst_xz h hc.ax0 hc.ax1 _ ?_ _ (degree_xz j i)]
  · have e0 : ∀ l : Fin d, ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] ((0, l) : Fin 2 × Fin d).1
        ((0, l) : Fin 2 × Fin d).2 = X ((0 : Fin 2), l) := fun l => rfl
    have e1 : ∀ m : Fin d, ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] ((1, m) : Fin 2 × Fin d).1
        ((1, m) : Fin 2 × Fin d).2 = rename (eZ d) (B.actK k (star a) m) := fun m => eval_second_point_rename _
    simp only [e0, e1, coeff_xz_X_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · rintro ⟨j', i'⟩
    fin_cases j'
    · exact constantCoeff_X _
    · show constantCoeff (ev (n := 2) ![pt k d 1] (B.actK k (star a) i')) = 0
      rw [eval_second_point_rename, constantCoeff_rename, const_actK]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
