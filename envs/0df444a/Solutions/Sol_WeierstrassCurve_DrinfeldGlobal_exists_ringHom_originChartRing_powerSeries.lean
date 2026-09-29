-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/56c9add7-ab7c-58c6-b1f4-9ba0bdd30661

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_powerSeries

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace FormalChartAux
open HomogeneousLocalization

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)
  {B : Type u} [CommRing B] [Algebra T B]

def RelB (x v : B) : Prop :=
  v + algebraMap T B W.a₁ * x * v + algebraMap T B W.a₃ * v ^ 2 =
    x ^ 3 + algebraMap T B W.a₂ * x ^ 2 * v + algebraMap T B W.a₄ * x * v ^ 2 + algebraMap T B W.a₆ * v ^ 3

noncomputable def evalAtB (x v : B) (h : RelB W x v) :
    ProjModelRingCR W →+* B :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom (algebraMap T B) ![x, 1, v]) fun a ha => by
    refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker _) (projModelHomogeneousIdealCR_toIdeal W ▸ ha)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    have e : W.polynomial = MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 + MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2
        + MvPolynomial.C W.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2
        - (MvPolynomial.X 0 ^ 3 + MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2
          + MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 + MvPolynomial.C W.a₆ * MvPolynomial.X 2 ^ 3) := rfl
    rw [e]
    simp only [MvPolynomial.coe_eval₂Hom, map_sub, map_add, map_mul, map_pow, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    have h' := h
    unfold RelB at h'
    linear_combination h'

lemma evalAtB_mk (x v : B) (h : RelB W x v) (p : MvPolynomial (Fin 3) T) :
    evalAtB W x v h (Ideal.Quotient.mk _ p) = MvPolynomial.eval₂ (algebraMap T B) ![x, 1, v] p := rfl

lemma evalAtB_Y (x v : B) (h : RelB W x v) : evalAtB W x v h (coord W 1) = 1 := by
  rw [show coord W 1 = Ideal.Quotient.mk _ (MvPolynomial.X 1) from rfl, evalAtB_mk, MvPolynomial.eval₂_X]; rfl

noncomputable def chartMapB (x v : B) (h : RelB W x v) : OriginChartRing W →+* B :=
  (IsLocalization.Away.lift (coord W 1) (g := evalAtB W x v h) ((evalAtB_Y W x v h).symm ▸ isUnit_one)).comp
    (algebraMap (OriginChartRing W) (Localization.Away (coord W 1)))

lemma chartMapB_mk_coord (x v : B) (h : RelB W x v) (i : Fin 3) (hi : coord W i ∈ projModelGradingCR W (1 • 1)) :
    chartMapB W x v h (Away.mk (projModelGradingCR W) (coord_mem W 1) 1 (coord W i) hi) =
      MvPolynomial.eval₂ (algebraMap T B) ![x, 1, v] (MvPolynomial.X i) := by
  simp only [chartMapB, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  have h1 : (Localization.mk (coord W i) ⟨coord W 1 ^ 1, ⟨1, rfl⟩⟩ : Localization.Away (coord W 1)) *
      algebraMap _ _ (coord W 1 ^ 1) = algebraMap _ _ (coord W i) := by
    rw [Localization.mk_eq_mk']; exact IsLocalization.mk'_spec _ _ _
  have h2 := congrArg (IsLocalization.Away.lift (coord W 1) (g := evalAtB W x v h) ((evalAtB_Y W x v h).symm ▸ isUnit_one)) h1
  have hY1 : evalAtB W x v h (coord W 1 ^ 1) = 1 := by rw [pow_one, evalAtB_Y]
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, hY1, mul_one] at h2
  rw [h2]
  rfl

lemma chartMapB_xOverY (x v : B) (h : RelB W x v) : chartMapB W x v h (xOverY W) = x := by
  rw [xOverY, chartMapB_mk_coord, MvPolynomial.eval₂_X]; rfl

lemma chartMapB_zOverY (x v : B) (h : RelB W x v) : chartMapB W x v h (zOverY W) = v := by
  rw [zOverY, chartMapB_mk_coord, MvPolynomial.eval₂_X]; rfl

lemma chartMapB_sc (x v : B) (h : RelB W x v) (t : T) :
    chartMapB W x v h (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      algebraMap T B t := by
  simp only [chartMapB, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply]
  have hval : (fromZeroRingHom (projModelGradingCR W) (Submonoid.powers (coord W 1)) (algebraMap T ((projModelGradingCR W) 0) t)).val =
      algebraMap (ProjModelRingCR W) (Localization.Away (coord W 1)) (algebraMap T (ProjModelRingCR W) t) := rfl
  rw [hval, IsLocalization.Away.lift_eq]
  show MvPolynomial.eval₂ (algebraMap T B) ![x, 1, v] (MvPolynomial.C t) = algebraMap T B t
  exact MvPolynomial.eval₂_C _ _ _

end FormalChartAux

open FormalChartAux HomogeneousLocalization in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) :
    ∃ Φ : OriginChartRing W →+* PowerSeries T,
      (∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
        PowerSeries.C t) ∧ Φ (xOverY W) = - PowerSeries.X ∧ Φ (zOverY W) = - W.formalW := by
  have h : (- W.formalW) + algebraMap T (PowerSeries T) W.a₁ * (- PowerSeries.X) * (- W.formalW) +
      algebraMap T (PowerSeries T) W.a₃ * (- W.formalW) ^ 2 =
      (- PowerSeries.X) ^ 3 + algebraMap T (PowerSeries T) W.a₂ * (- PowerSeries.X) ^ 2 * (- W.formalW) +
        algebraMap T (PowerSeries T) W.a₄ * (- PowerSeries.X) * (- W.formalW) ^ 2 +
        algebraMap T (PowerSeries T) W.a₆ * (- W.formalW) ^ 3 := by
    have e := W.formalW_eq
    simp only [PowerSeries.algebraMap_eq]
    linear_combination (-1 : PowerSeries T) * e
  have hR : RelB (B := PowerSeries T) W (-PowerSeries.X) (-W.formalW) := h
  exact ⟨chartMapB W (-PowerSeries.X) (-W.formalW) hR, fun t => (chartMapB_sc W _ _ hR t).trans (by rw [PowerSeries.algebraMap_eq]),
    chartMapB_xOverY W _ _ hR, chartMapB_zOverY W _ _ hR⟩

end S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_powerSeries
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_powerSeries (solution)
