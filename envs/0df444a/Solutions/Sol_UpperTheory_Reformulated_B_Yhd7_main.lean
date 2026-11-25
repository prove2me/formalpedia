-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yhd7.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:00:22.162468+00:00
-- url     : https://prove2.me/submissions/b140838d-e3b2-48ef-884b-9821eacff165

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsSideBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace EqOneOfPowersNearOne
private lemma key {R : Type} [NormedRing R] [NormedAlgebra ℂ R] {a : R}
    (h : ∀ (p : ℕ), ‖a ^ p - (1 : R)‖ < (1 / 2 : ℝ)) (N : ℕ) :
    (N : ℝ) * ‖a - 1‖ < ‖a - 1‖ * (N / 2) + 1 / 2 := by
  set S : R := ∑ k ∈ Finset.range N, a ^ k with hS
  have hgeom : S * (a - 1) = a ^ N - 1 := geom_sum_mul a N
  have hdiff : (N : R) - S = ∑ k ∈ Finset.range N, ((1 : R) - a ^ k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hbound : ‖(N : R) - S‖ ≤ N / 2 := by
    rw [hdiff]
    calc ‖∑ k ∈ Finset.range N, ((1 : R) - a ^ k)‖
        ≤ ∑ k ∈ Finset.range N, ‖(1 : R) - a ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, (1 / 2 : ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_sub_rev]; exact (h k).le
      _ = N / 2 := by simp; ring
  have hnorm : ‖(N : R) * (a - 1)‖ = (N : ℝ) * ‖a - 1‖ := by
    have : (N : R) * (a - 1) = (N : ℂ) • (a - 1) := by
      rw [Algebra.smul_def]; simp
    rw [this, norm_smul]; simp
  have hsplit : (N : R) * (a - 1) = ((N : R) - S) * (a - 1) + S * (a - 1) := by
    rw [sub_mul]; abel
  calc (N : ℝ) * ‖a - 1‖ = ‖(N : R) * (a - 1)‖ := hnorm.symm
    _ ≤ ‖((N : R) - S) * (a - 1)‖ + ‖S * (a - 1)‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖(N : R) - S‖ * ‖a - 1‖ + ‖a ^ N - 1‖ := by
        rw [hgeom]; gcongr; exact norm_mul_le _ _
    _ < ‖a - 1‖ * (N / 2) + 1 / 2 := by
        have := h N
        nlinarith [norm_nonneg (a - 1)]
end EqOneOfPowersNearOne
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yhd7
theorem _root_.solution :
    ∀ {R : Type} [inst : NormedRing R] [NormedAlgebra ℂ R] {a : R},
      (∀ (p : ℕ), ‖a ^ p - (1 : R)‖ < (1 / 2 : ℝ)) → a = (1 : R) := by
  intro R _ _ a h
  by_contra hne
  have hpos : 0 < ‖a - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖a - 1‖)
  have hk := EqOneOfPowersNearOne.key h N
  have h1 : 1 < (N : ℝ) * ‖a - 1‖ := by
    rw [div_lt_iff₀ hpos] at hN; linarith
  nlinarith
end UpperTheory.Reformulated.B.Yhd7
