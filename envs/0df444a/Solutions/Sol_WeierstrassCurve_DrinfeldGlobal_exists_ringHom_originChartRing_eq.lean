-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_ringHom_originChartRing_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9adf1ae0-34ce-5885-8bf1-6c6f2cd0dee2

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ChartHomAux

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)
variable {B : Type u} [CommRing B] [Algebra T B]

def Rel (x v : B) : Prop :=
  v + algebraMap T B W.a₁ * x * v + algebraMap T B W.a₃ * v ^ 2 =
    x ^ 3 + algebraMap T B W.a₂ * x ^ 2 * v + algebraMap T B W.a₄ * x * v ^ 2 + algebraMap T B W.a₆ * v ^ 3

noncomputable def evalAt (x v : B) (h : Rel W x v) : ProjModelRingCR W →+* B :=
  Ideal.Quotient.lift _ (MvPolynomial.aeval ![x, 1, v]).toRingHom fun a ha => by
    refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker _) (projModelHomogeneousIdealCR_toIdeal W ▸ ha)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    have e : W.polynomial = MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 + MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2
        + MvPolynomial.C W.a₃ * MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2
        - (MvPolynomial.X 0 ^ 3 + MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2
          + MvPolynomial.C W.a₄ * MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 + MvPolynomial.C W.a₆ * MvPolynomial.X 2 ^ 3) := rfl
    rw [e]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_add, map_mul, map_pow, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    have h' := h
    unfold Rel at h'
    linear_combination h'

lemma evalAt_mk (x v : B) (h : Rel W x v) (p : MvPolynomial (Fin 3) T) :
    evalAt W x v h (Ideal.Quotient.mk _ p) = MvPolynomial.aeval ![x, 1, v] p := rfl

lemma evalAt_Y (x v : B) (h : Rel W x v) : evalAt W x v h (coord W 1) = 1 := by
  rw [show coord W 1 = Ideal.Quotient.mk _ (MvPolynomial.X 1) from rfl, evalAt_mk, MvPolynomial.aeval_X]; rfl

noncomputable def chartMap (x v : B) (h : Rel W x v) : OriginChartRing W →+* B :=
  (IsLocalization.Away.lift (coord W 1) (g := evalAt W x v h) ((evalAt_Y W x v h).symm ▸ isUnit_one)).comp
    (algebraMap (OriginChartRing W) (Localization.Away (coord W 1)))

lemma chartMap_mk_coord (x v : B) (h : Rel W x v) (i : Fin 3) (hi : coord W i ∈ projModelGradingCR W (1 • 1)) :
    chartMap W x v h (Away.mk (projModelGradingCR W) (coord_mem W 1) 1 (coord W i) hi) =
      MvPolynomial.aeval ![x, 1, v] (MvPolynomial.X i : MvPolynomial (Fin 3) T) := by
  simp only [chartMap, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  have h1 : (Localization.mk (coord W i) ⟨coord W 1 ^ 1, ⟨1, rfl⟩⟩ : Localization.Away (coord W 1)) *
      algebraMap _ _ (coord W 1 ^ 1) = algebraMap _ _ (coord W i) := by
    rw [Localization.mk_eq_mk']; exact IsLocalization.mk'_spec _ _ _
  have h2 := congrArg (IsLocalization.Away.lift (coord W 1) (g := evalAt W x v h) ((evalAt_Y W x v h).symm ▸ isUnit_one)) h1
  have hY1 : evalAt W x v h (coord W 1 ^ 1) = 1 := by rw [pow_one, evalAt_Y]
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, hY1, mul_one] at h2
  rw [h2]
  rfl

lemma chartMap_xOverY (x v : B) (h : Rel W x v) : chartMap W x v h (xOverY W) = x := by
  rw [xOverY, chartMap_mk_coord, MvPolynomial.aeval_X]; rfl

lemma chartMap_zOverY (x v : B) (h : Rel W x v) : chartMap W x v h (zOverY W) = v := by
  rw [zOverY, chartMap_mk_coord, MvPolynomial.aeval_X]; rfl

lemma chartMap_sc (x v : B) (h : Rel W x v) (t : T) :
    chartMap W x v h (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      algebraMap T B t := by
  simp only [chartMap, RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply]
  have hval : (fromZeroRingHom (projModelGradingCR W) (Submonoid.powers (coord W 1)) (algebraMap T ((projModelGradingCR W) 0) t)).val =
      algebraMap (ProjModelRingCR W) (Localization.Away (coord W 1)) (algebraMap T (ProjModelRingCR W) t) := rfl
  rw [hval, IsLocalization.Away.lift_eq]
  show MvPolynomial.aeval ![x, 1, v] (MvPolynomial.C t : MvPolynomial (Fin 3) T) = algebraMap T B t
  exact MvPolynomial.aeval_C _ _

end ChartHomAux

theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) {B : Type u} [CommRing B] [Algebra T B] (x v : B)
    (h : v + algebraMap T B W.a₁ * x * v + algebraMap T B W.a₃ * v ^ 2 =
      x ^ 3 + algebraMap T B W.a₂ * x ^ 2 * v + algebraMap T B W.a₄ * x * v ^ 2 + algebraMap T B W.a₆ * v ^ 3) :
    ∃ χ : OriginChartRing W →+* B,
      (∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
        algebraMap T B t) ∧ χ (xOverY W) = x ∧ χ (zOverY W) = v := by
  have hrel : ChartHomAux.Rel (W : WeierstrassCurve.Projective T) x v := h
  exact ⟨ChartHomAux.chartMap (W : WeierstrassCurve.Projective T) x v hrel,
    ChartHomAux.chartMap_sc _ x v hrel, ChartHomAux.chartMap_xOverY _ x v hrel, ChartHomAux.chartMap_zOverY _ x v hrel⟩

end S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_eq
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_ringHom_originChartRing_eq (solution)
