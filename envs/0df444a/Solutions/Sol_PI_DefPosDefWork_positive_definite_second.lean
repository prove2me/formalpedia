-- Prove2me | solution 1 for PI.DefPosDefWork.positive_definite_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:45:09.502126+00:00
-- url     : https://prove2.me/submissions/f994073d-9150-42c6-a490-ce1c935d8f75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_PositiveDefiniteSecond
import Theorems.Thm_PI_DefPosDefWork_posDef_of_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DefPosDefWork
open Matrix ComplexOrder
namespace PI.DefPosDefWork
theorem _root_.solution : Step2 := by
  intro F E _ _ _ _ _ hF σ k J _ hH hD h1 φ
  obtain ⟨r, hr⟩ := hF (φ.comp (algebraMap F E))
  have hr' : ∀ a, φ (algebraMap F E a) = (r a : ℂ) := fun a => hr a
  have hJ : ∀ i j, σ (J j i) = J i j := fun i j => congrFun (congrFun hH i) j
  have hst : ∀ y, star (φ y) = φ (σ y) := fun y => (h1 φ y).symm
  have hMh : (J.map φ).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, hst, hJ]
  have hQ : ∀ x : Fin k → E, star (fun i => φ (x i)) ⬝ᵥ (J.map φ *ᵥ (fun i => φ (x i)))
      = φ (hform (σ : E →+* E) J x x) := by
    intro x
    simp only [dotProduct, mulVec, hform, Pi.star_apply, hst, Matrix.map_apply, map_sum, map_mul,
      Finset.mul_sum, mul_assoc]
    rfl
  have hdet : J.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hJv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr h0
    have h0' : hform (σ : E →+* E) J v v = 0 := by
      have e : hform (σ : E →+* E) J v v = ∑ i, (σ : E →+* E) (v i) * (J *ᵥ v) i := by
        simp only [hform, mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rw [e, hJv]
      simp
    rcases hD r with h | h
    · obtain ⟨a, ha, ha'⟩ := h v hv
      rw [h0'] at ha
      have ha0 : a = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).mp ha
      rw [ha0, map_zero] at ha'
      exact lt_irrefl _ ha'
    · obtain ⟨a, ha, ha'⟩ := h v hv
      rw [h0'] at ha
      have ha0 : a = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).mp ha
      rw [ha0, map_zero] at ha'
      exact lt_irrefl _ ha'
  have hMu : IsUnit (J.map φ) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hdet
  have hMr : (∀ t : E, (φ t).im = 0) → ∀ i j, ((J.map φ) i j).im = 0 := fun ht i j => ht (J i j)
  have hQ0 : ∀ x : Fin k → E, x = 0 → hform (σ : E →+* E) J x x = 0 := by
    intro x hx
    subst hx
    simp [hform]
  rcases hD r with h | h
  · left
    refine posDef_of_points φ _ hMh hMu hMr fun x => ?_
    rw [hQ]
    by_cases hx : x = 0
    · rw [hQ0 x hx]
      simp
    · obtain ⟨a, ha, ha'⟩ := h x hx
      rw [← ha, hr']
      simpa using ha'.le
  · right
    refine posDef_of_points φ _ hMh.neg hMu.neg (fun ht i j => by simpa using hMr ht i j) fun x => ?_
    rw [Matrix.neg_mulVec, dotProduct_neg, hQ]
    by_cases hx : x = 0
    · rw [hQ0 x hx]
      simp
    · obtain ⟨a, ha, ha'⟩ := h x hx
      rw [← ha, hr']
      simp
      linarith
end PI.DefPosDefWork
