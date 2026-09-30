-- Prove2me | solution 1 for UnderstandingML.rip_exact_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T11:47:25.421205+00:00
-- url     : https://prove2.me/submissions/2c55161f-e041-4b80-9ca1-aa423a5de990

import Mathlib
import Definitions.Def_UnderstandingML_DimReduction

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

theorem uml_l0Norm_sub_le {d : ℕ} (a b : Fin d → ℝ) :
    UnderstandingML.l0Norm (a - b) ≤ UnderstandingML.l0Norm a + UnderstandingML.l0Norm b := by
  classical
  unfold UnderstandingML.l0Norm
  calc _ ≤ ((Finset.univ.filter fun i => a i ≠ 0) ∪ (Finset.univ.filter fun i => b i ≠ 0)).card := by
        apply Finset.card_le_card
        intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Pi.sub_apply]
        intro h
        by_contra hc
        rw [not_or, not_not, not_not] at hc
        exact h (by rw [hc.1, hc.2, sub_self])
    _ ≤ _ := Finset.card_union_le _ _

open MeasureTheory ProbabilityTheory UnderstandingML in
theorem solution {n d s : ℕ} (ε : ℝ) (hε : ε < 1) (W : Matrix (Fin n) (Fin d) ℝ)
    (hW : IsRIP ε (2 * s) W) (x xt : Fin d → ℝ) (hx : l0Norm x ≤ s)
    (hy : W.mulVec xt = W.mulVec x) (hmin : ∀ v, W.mulVec v = W.mulVec x → l0Norm xt ≤ l0Norm v) :
    xt = x := by
  have hxt : l0Norm xt ≤ s := (hmin x rfl).trans hx
  have hsub : l0Norm (xt - x) ≤ 2 * s := (uml_l0Norm_sub_le xt x).trans (by omega)
  by_contra hne
  have hne' : xt - x ≠ 0 := sub_ne_zero.mpr hne
  have h := hW (xt - x) hne' hsub
  have hz : W.mulVec (xt - x) = 0 := by rw [Matrix.mulVec_sub, hy, sub_self]
  have h0 : sqNorm (0 : Fin n → ℝ) = 0 := by simp [sqNorm]
  rw [hz, h0, zero_div, zero_sub, abs_neg, abs_one] at h
  linarith
