-- Prove2me | solution 1 for PrefixVR.eq_26
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:08:09.636733+00:00
-- url     : https://prove2.me/submissions/9f2311bb-56cd-4bf4-8e22-d910b09b24e1

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_PrefixVR_Variation
import Definitions.Def_PrefixVR_Assumption3

open PrefixVR in
theorem solution {n d : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL : 0 < L)
    (hA1 : ∀ i, ConvexOptAlg.SmoothGD.IsBetaSmooth (fi i) (g i) L) :
    Assumption3 fi g L L := by
  have hgrad : ∀ x, HasGradientAt (KatyushaNs.favg fi) (gradAvg g x) x := by
    intro x
    rw [hasGradientAt_iff_hasFDerivAt]
    have hs : HasFDerivAt (fun y => ∑ i, fi i y)
        (∑ i, InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (g i x)) x :=
      HasFDerivAt.fun_sum (fun i _ => hasGradientAt_iff_hasFDerivAt.mp ((hA1 i).2.1 x))
    have h2 := hs.const_mul ((n : ℝ)⁻¹)
    have heq : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (gradAvg g x) =
        (n : ℝ)⁻¹ • ∑ i, InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (g i x) := by
      unfold gradAvg
      simp only [map_smulₛₗ, map_sum, RCLike.conj_to_real]
    rw [heq]
    exact h2
  have e : ∀ x y, gradAvg g x - gradAvg g y = (n : ℝ)⁻¹ • ∑ i, (g i x - g i y) := by
    intro x y
    unfold gradAvg
    rw [← smul_sub, ← Finset.sum_sub_distrib]
  have hvi : ∀ i x y, ‖g i x - g i y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    intro i x y
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hA1 i).2.2 x y) 2
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨fun i x => (hA1 i).2.1 x, hL, ⟨hL.le, hgrad, fun x y => ?_⟩, hL.le, fun x y => ?_⟩
    · simp [gradAvg] <;> positivity
    · simp <;> positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun i x => (hA1 i).2.1 x, hL, ⟨hL.le, hgrad, fun x y => ?_⟩, hL.le, fun x y => ?_⟩
  · rw [e, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    calc (n : ℝ)⁻¹ * ‖∑ i, (g i x - g i y)‖ ≤ (n : ℝ)⁻¹ * ∑ i, ‖g i x - g i y‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, L * ‖x - y‖ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hA1 i).2.2 x y) (by positivity)
      _ = L * ‖x - y‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hn'.ne', one_mul]
  · have hv : ∀ i, g i x - g i y - gradAvg g x + gradAvg g y
        = (g i x - g i y) - (gradAvg g x - gradAvg g y) := fun i => by abel
    simp_rw [hv]
    obtain ⟨w, hw⟩ : ∃ w, w = gradAvg g x - gradAvg g y := ⟨_, rfl⟩
    rw [← hw]
    have hsumv : ∑ i, (g i x - g i y) = (n : ℝ) • w := by
      rw [hw, e, smul_smul, mul_inv_cancel₀ hn'.ne', one_smul]
    have hexp : ∑ i, ‖(g i x - g i y) - w‖ ^ 2
        = ∑ i, ‖g i x - g i y‖ ^ 2 - 2 * inner ℝ (∑ i, (g i x - g i y)) w + n * ‖w‖ ^ 2 := by
      simp_rw [norm_sub_sq_real]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsumv, real_inner_smul_left, real_inner_self_eq_norm_sq] at hexp
    have hb : ∑ i, ‖g i x - g i y‖ ^ 2 ≤ ∑ _i : Fin n, L ^ 2 * ‖x - y‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hvi i x y
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
    rw [hexp, inv_mul_le_iff₀ hn']
    nlinarith [mul_nonneg hn'.le (sq_nonneg ‖w‖)]
