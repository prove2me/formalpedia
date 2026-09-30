-- Prove2me | solution 1 for UnderstandingML.covering_affine
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T11:31:12.3428+00:00
-- url     : https://prove2.me/submissions/a8d7045d-9aac-47b4-839f-fb528e23ee54

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

theorem uml_eucNorm_smul {m : ℕ} (c : ℝ) (w : Fin m → ℝ) :
    UnderstandingML.eucNorm (c • w) = |c| * UnderstandingML.eucNorm w := by
  unfold UnderstandingML.eucNorm
  have h : ∑ i, (c • w) i ^ 2 = c ^ 2 * ∑ i, w i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

open MeasureTheory UnderstandingML in
theorem solution {m : ℕ} (A : Set (Fin m → ℝ)) (c : ℝ) (hc : 0 < c) (a₀ : Fin m → ℝ)
    (r : ℝ) (hr : 0 < r) :
    coveringNumber (c * r) ((fun a ↦ c • a + a₀) '' A) ≤ coveringNumber r A := by
  refine uml_cover_image_le A (fun a ↦ c • a + a₀) c hc.le (fun a b => ?_) r
  have e : (c • a + a₀) - (c • b + a₀) = c • (a - b) := by
    rw [smul_sub]; abel
  simp only [e, uml_eucNorm_smul, abs_of_pos hc, le_refl]
