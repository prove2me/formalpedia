-- Prove2me | solution 1 for UnderstandingML.covering_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T11:35:50.238981+00:00
-- url     : https://prove2.me/submissions/396ad76f-fc54-48da-8c46-a6e93109aede

import Mathlib
import Definitions.Def_UnderstandingML_Covering

set_option autoImplicit false

open MeasureTheory

theorem uml_cover_image_le {m : ℕ} (A : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → (Fin m → ℝ))
    (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ a b, UnderstandingML.eucNorm (f a - f b) ≤ K * UnderstandingML.eucNorm (a - b))
    (r : ℝ) :
    UnderstandingML.coveringNumber (K * r) (f '' A) ≤ UnderstandingML.coveringNumber r A := by
  classical
  unfold UnderstandingML.coveringNumber
  refine le_iInf₂ fun A' hA' => ?_
  have hc : UnderstandingML.IsCover (K * r) (f '' A) (A'.image f) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨a', ha', hd⟩ := hA' a ha
    exact ⟨f a', Finset.mem_image_of_mem f ha', (hf a a').trans (mul_le_mul_of_nonneg_left hd hK)⟩
  refine (iInf₂_le (A'.image f) hc).trans ?_
  exact_mod_cast Finset.card_image_le

open MeasureTheory UnderstandingML in
theorem solution {m : ℕ} (A : Set (Fin m → ℝ)) (ρ : NNReal) (φ : Fin m → ℝ → ℝ)
    (hφ : ∀ i, LipschitzWith ρ (φ i)) (r : ℝ) :
    coveringNumber (ρ * r) ((fun a i ↦ φ i (a i)) '' A) ≤ coveringNumber r A := by
  refine uml_cover_image_le A (fun a i ↦ φ i (a i)) ρ ρ.2 (fun a b => ?_) r
  unfold eucNorm
  have hsum : ∑ i, ((fun i ↦ φ i (a i)) - (fun i ↦ φ i (b i))) i ^ 2 ≤
      (ρ : ℝ) ^ 2 * ∑ i, (a - b) i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h := (hφ i).dist_le_mul (a i) (b i)
    rw [Real.dist_eq, Real.dist_eq] at h
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow, sq_abs] at h2
    simpa only [Pi.sub_apply] using h2
  calc Real.sqrt (∑ i, ((fun i ↦ φ i (a i)) - (fun i ↦ φ i (b i))) i ^ 2)
      ≤ Real.sqrt ((ρ : ℝ) ^ 2 * ∑ i, (a - b) i ^ 2) := Real.sqrt_le_sqrt hsum
    _ = (ρ : ℝ) * Real.sqrt (∑ i, (a - b) i ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (NNReal.coe_nonneg ρ)]
