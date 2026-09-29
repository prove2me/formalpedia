-- Prove2me | solution 1 for P2M.Dup.WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3369a3dc-414c-5f31-8f50-f5222dd637e6

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal

p2m_open "Polynomial WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve.Affine.CoordinateRing"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map Affine.CoordinateRing mk Affine.Point"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "Equation CoordinateRing map Point CoordinateRing.basis polynomial"
namespace CoordinateRing
p2m_export "WeierstrassCurve.Affine.CoordinateRing" "XYIdeal quotientXYIdealEquiv YClass mk map XClass"
namespace DetInfra
p2m_open "WeierstrassCurve.Affine.CoordinateRing WeierstrassCurve.Affine WeierstrassCurve"

variable {F : Type*} [Field F] {W : Affine F}

lemma XYIdeal_eq_map (x : F) (y : F[X]) :
    XYIdeal W x y = Ideal.map (mk W) (Ideal.span {C (X - C x), Y - C y}) := by
  simp only [XYIdeal, XClass, YClass, ← Set.image_pair, ← Ideal.map_span]

lemma mk_mem_XYIdeal_of_evalEval_eq_zero (x y : F) {p : F[X][Y]} (hp : p.evalEval x y = 0) :
    mk W p ∈ XYIdeal W x (C y) := by
  rw [XYIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ (mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr hp)

lemma isMaximal_XYIdeal' {x y : F} (h : W.Equation x y) : (XYIdeal W x (C y)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    MulEquiv.isField (Field.toIsField F) (quotientXYIdealEquiv (W' := W) h).toMulEquiv

theorem isMaximal_iff_exists_eq_XYIdeal' [IsAlgClosed F] (I : Ideal W.CoordinateRing) :
    I.IsMaximal ↔ ∃ x y : F, W.Equation x y ∧ I = XYIdeal W x (C y) := by
  constructor
  · intro hI
    letI := Ideal.Quotient.field I
    have : Module.Finite F (W.CoordinateRing ⧸ I) :=
      finite_of_finite_type_of_isJacobsonRing F _
    have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F)
      (K := W.CoordinateRing ⧸ I)
    obtain ⟨x, hx⟩ := hbij.2 (Ideal.Quotient.mk I (mk W (C X)))
    obtain ⟨y, hy⟩ := hbij.2 (Ideal.Quotient.mk I (mk W Y))
    have hxI : XClass W x ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [XClass, map_sub, ← hx, sub_eq_zero]
      rfl
    have hyI : YClass W (C y) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [YClass, map_sub, ← hy, sub_eq_zero]
      rfl
    have hle : XYIdeal W x (C y) ≤ I :=
      Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨hxI, Set.singleton_subset_iff.mpr hyI⟩)
    have heq : W.Equation x y := by
      by_contra hne
      refine hI.ne_top (I.eq_top_of_isUnit_mem (hle <| mk_mem_XYIdeal_of_evalEval_eq_zero x y
        (p := W.polynomial - C (C (W.polynomial.evalEval x y))) ?_) ?_)
      · simp only [evalEval_sub, evalEval_CC, sub_self]
      · rw [map_sub, AdjoinRoot.mk_self, zero_sub, IsUnit.neg_iff]
        exact (Ne.isUnit hne).map (algebraMap F W.CoordinateRing)
    exact ⟨x, y, heq, ((isMaximal_XYIdeal' heq).eq_of_le hI.ne_top hle).symm⟩
  · rintro ⟨x, y, h, rfl⟩
    exact isMaximal_XYIdeal' h

scoped instance : Module.Finite F[X] W.CoordinateRing := Module.Finite.of_basis (CoordinateRing.basis W)

lemma isMaximal_of_isPrime_of_ne_bot (P : Ideal W.CoordinateRing) [P.IsPrime] (hP : P ≠ ⊥) :
    P.IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := F[X]) P <|
    IsPrime.to_maximal_ideal (Ideal.under_ne_bot F[X] hP)

end WeierstrassCurve.Affine.CoordinateRing.DetInfra
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve.Affine.CoordinateRing P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve.Affine.CoordinateRing.DetInfra"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve.Affine.CoordinateRing"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve.Affine"
p2m_reactivate "P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal.WeierstrassCurve"

open WeierstrassCurve.Affine.CoordinateRing.DetInfra

theorem solution {K : Type*} [Field K] {W : Affine K} [IsAlgClosed K] {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] : ∃ a b : K, W.Equation a b ∧ P = XYIdeal W a (C b) :=
  (isMaximal_iff_exists_eq_XYIdeal' P).mp (isMaximal_of_isPrime_of_ne_bot P hP)

end S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal
end P2MW
export P2MW.S_WeierstrassCurve_Affine_CoordinateRing_exists_eq_XYIdeal (solution)
