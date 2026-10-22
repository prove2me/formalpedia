-- Prove2me | solution 1 for RInf.reid_two_classes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:10:51.774555+00:00
-- url     : https://prove2.me/submissions/761fa9ff-7408-4755-a3f1-21f876246d0b

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid
open RInf

noncomputable def g74p_L {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int)) :
    (Fin k → Int) →ₗ[ℤ] (Fin k → Int) :=
  LinearMap.id - m.toAddMonoidHom.toIntLinearMap

theorem g74p_L_apply {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int)) (z : Fin k → Int) :
    Matrix.mulVec (LinearMap.toMatrix' (g74p_L m)) z = z - m z := by
  rw [LinearMap.toMatrix'_mulVec]; rfl

noncomputable def g74p_Lp {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int)) :
    (Fin k → Int) →ₗ[ℤ] (Fin k → Int) :=
  LinearMap.id + m.toAddMonoidHom.toIntLinearMap

theorem g74p_Lp_apply {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int)) (z : Fin k → Int) :
    Matrix.mulVec (LinearMap.toMatrix' (g74p_Lp m)) z = z + m z := by
  rw [LinearMap.toMatrix'_mulVec]; rfl

theorem g74p_mod2 {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int)) :
    (Int.castRingHom (ZMod 2)).mapMatrix (LinearMap.toMatrix' (g74p_L m)) =
    (Int.castRingHom (ZMod 2)).mapMatrix (LinearMap.toMatrix' (g74p_Lp m)) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, g74p_L,
    g74p_Lp, LinearMap.sub_apply, LinearMap.add_apply, Pi.sub_apply, Pi.add_apply,
    eq_intCast, Int.cast_sub, Int.cast_add, sub_eq_add_neg, LinearMap.neg_apply, Pi.neg_apply,
    Int.cast_neg, ZMod.neg_eq_self_mod_two]

theorem g74p_not_surj {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int))
    (h : ∃ v : Fin k → Int, v ≠ 0 ∧ (m v = v ∨ m v = -v)) :
    ∃ x : Fin k → Int, ∀ z, x ≠ z - m z := by
  by_contra hc
  have hs : Function.Surjective (Matrix.mulVec (LinearMap.toMatrix' (g74p_L m))) := by
    intro x
    by_contra hx
    exact hc ⟨x, fun z hz => hx ⟨z, by rw [g74p_L_apply, hz]⟩⟩
  rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at hs
  obtain ⟨v, hv0, hv | hv⟩ := h
  · have hdet : (LinearMap.toMatrix' (g74p_L m)).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      exact ⟨v, hv0, by rw [g74p_L_apply, hv, sub_self]⟩
    rw [hdet] at hs
    exact not_isUnit_zero hs
  · have hdet : (LinearMap.toMatrix' (g74p_Lp m)).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      exact ⟨v, hv0, by rw [g74p_Lp_apply, hv, add_neg_cancel]⟩
    have hu := hs.map (Int.castRingHom (ZMod 2))
    rw [RingHom.map_det, g74p_mod2, ← RingHom.map_det, hdet, map_zero] at hu
    exact not_isUnit_zero hu

theorem solution {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int))
    (h : ∃ v : Fin k → Int, v ≠ 0 ∧ (m v = v ∨ m v = -v)) :
    ∃ x y : Fin k → Int, ¬ TwistedConjAdd m x y := by
  obtain ⟨x, hx⟩ := g74p_not_surj m h
  refine ⟨x, 0, fun ⟨z, hz⟩ => hx z ?_⟩
  rw [hz, add_zero]
