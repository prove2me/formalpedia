-- Prove2me | solution 1 for RInf.eigen_one_inf
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:09:50.169289+00:00
-- url     : https://prove2.me/submissions/ae10702f-27c1-4805-9991-689ffb488bbf

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

theorem g74p_functional {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int))
    (h : HasEigenOne m) : ∃ w : Fin k → Int, w ≠ 0 ∧ ∀ z, w ⬝ᵥ (z - m z) = 0 := by
  obtain ⟨v, hv0, hv⟩ := h
  have hdet : (LinearMap.toMatrix' (g74p_L m)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv0, by rw [g74p_L_apply, hv, sub_self]⟩
  rw [← Matrix.exists_vecMul_eq_zero_iff] at hdet
  obtain ⟨w, hw0, hw⟩ := hdet
  refine ⟨w, hw0, fun z => ?_⟩
  rw [← g74p_L_apply, Matrix.dotProduct_mulVec, hw, zero_dotProduct]

theorem g74p_eigen_one_inf {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int))
    (h : HasEigenOne m) : ReidInfAdd m := by
  obtain ⟨w, hw0, hw⟩ := g74p_functional m h
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hc; exact hw0 (funext fun t => by_contra fun ht => hc ⟨t, ht⟩)
  refine ⟨fun i => Pi.single j (i : ℤ), fun i i' hii ⟨z, hz⟩ => hii ?_⟩
  have h1 : Pi.single j (i : ℤ) - Pi.single j (i' : ℤ) = z - m z := by
    simp only at hz; rw [hz]; abel
  have h2 := hw z
  rw [← h1, dotProduct_sub, dotProduct_single, dotProduct_single, ← mul_sub] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hj
  · exact_mod_cast sub_eq_zero.1 h3

theorem solution {k : Nat} (m : (Fin k → Int) ≃+ (Fin k → Int))
    (h : HasEigenOne m) : ReidInfAdd m := g74p_eigen_one_inf m h
