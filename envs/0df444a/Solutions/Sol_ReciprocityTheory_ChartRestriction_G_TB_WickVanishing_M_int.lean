-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.M_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:01:46.199255+00:00
-- url     : https://prove2.me/submissions/63e9e724-369c-4265-82f1-8b9335328300

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_first_point_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eval_second_point_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_degree_xz
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_const_actK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ad_side1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ad_side2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_low
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_expS_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gaugeBilinearTerm_eq_neg_double_sum


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
    (sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h) i j ∈ (algebraMap R k).range := by
  have k0 : ∀ i', constantCoeff (comp1 (B.actK k a) (pt k d 0 : Pt k 2 d) i') = 0 := fun i' => by
    have : comp1 (B.actK k a) (pt k d 0 : Pt k 2 d) i' = rename (eXv d) (B.actK k a i') := eval_first_point_rename _
    rw [this, constantCoeff_rename, const_actK]
  have k1 : ∀ i', constantCoeff (comp1 (B.actK k (star a)) (pt k d 1 : Pt k 2 d) i') = 0 := fun i' => by
    have : comp1 (B.actK k (star a)) (pt k d 1 : Pt k 2 d) i' = rename (eZ d) (B.actK k (star a) i') :=
      eval_second_point_rename _
    rw [this, constantCoeff_rename, const_actK]
  have kX : ∀ (j' : Fin 2) (i' : Fin d), constantCoeff (pt k d j' i' : PS k 2 d) = 0 := fun j' i' => constantCoeff_X _
  have c1 : ∀ j' i', constantCoeff ((![comp1 (B.actK k a) (pt k d 0), pt k d 1] : Fin 2 → Pt k 2 d) j' i') = 0 := by
    intro j' i'
    fin_cases j'
    exacts [k0 i', kX 1 i']
  have c2 : ∀ j' i', constantCoeff ((![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] : Fin 2 → Pt k 2 d) j' i') = 0 := by
    intro j' i'
    fin_cases j'
    exacts [kX 0 i', k1 i']
  have hord : ∀ e : Fin 2 × Fin d →₀ ℕ, e.degree < 2 → coeff e (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h) = 0 := fun e he => by
    rw [map_sub, coeff_ev_low B h hc _ c1 e he, coeff_ev_low B h hc _ c2 e he, sub_zero]
  have e := congrArg (coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1)) (hc.ad a)
  rw [coeff_expS_two _ hord _ (degree_xz j i), map_sub, coeff_ad_side1 B h hc a i j, coeff_ad_side2 B h hc a i j,
    coeff_map] at e
  refine ⟨-coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) (B.ad a), ?_⟩
  rw [map_neg, e]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, gaugeBilinearTerm_eq_neg_double_sum, neg_mul, mul_neg,
    Finset.sum_neg_distrib]
  have hc2 : ∑ x, dAct k B (star a) x i * coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), x) 1) h =
      ∑ m, coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), m) 1) h * dAct k B (star a) m i :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hc2]
  ring
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
