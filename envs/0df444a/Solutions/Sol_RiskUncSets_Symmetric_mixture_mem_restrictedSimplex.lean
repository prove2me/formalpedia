-- Prove2me | solution 1 for RiskUncSets.Symmetric.mixture_mem_restrictedSimplex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:41:38.736586+00:00
-- url     : https://prove2.me/submissions/65c7ffcd-04c7-44f9-b8ed-dbbd3cd70565

import Mathlib
import Definitions.Def_RiskUncSets_Symmetric_Setting

set_option autoImplicit false

namespace RiskUncSets.Symmetric.D6d844d3Aux

open RiskUncSets.Symmetric

lemma qbar_eq {N : ℕ} (j : Fin (Nhat N)) :
    qbar j = fun i : Fin N =>
      (1 / (N : ℝ)) * ((if (i : ℕ) < (j : ℕ) then (1 : ℝ) else 0) +
        (if (i : ℕ) + (j : ℕ) + 1 ≤ N then (1 : ℝ) else 0)) := by
  have hj : 2 * (j : ℕ) ≤ N := by
    have := j.isLt; unfold Nhat at this; omega
  funext i
  unfold qbar
  split_ifs <;> first | (exfalso; omega) | ring

lemma sum_ite_lt (N m : ℕ) (hm : m ≤ N) :
    (∑ i : Fin N, (if (i : ℕ) < m then (1 : ℝ) else 0)) = m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < m then (1 : ℝ) else 0) N]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Finset.range N).filter (fun i => i < m) = Finset.range m := by
    ext x; simp; omega
  rw [this, Finset.card_range]

lemma qbar_mem {N : ℕ} (hN : 0 < N) (j : Fin (Nhat N)) :
    qbar j ∈ restrictedSimplex N := by
  have hj : 2 * (j : ℕ) ≤ N := by
    have := j.isLt; unfold Nhat at this; omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [qbar_eq]
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · apply mul_nonneg (by positivity)
    apply add_nonneg <;> split_ifs <;> norm_num
  · rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_ite_lt N j (by omega)]
    have : (∑ i : Fin N, (if (i : ℕ) + (j : ℕ) + 1 ≤ N then (1 : ℝ) else 0))
        = ∑ i : Fin N, (if (i : ℕ) < N - (j : ℕ) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro i _
      congr 1; apply propext; omega
    rw [this, sum_ite_lt N (N - j) (by omega)]
    rw [Nat.cast_sub (by omega)]
    field_simp
    ring
  · intro a b hab
    have hab' : (a : ℕ) ≤ b := hab
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · split_ifs <;> (try (exfalso; omega)) <;> norm_num
    · split_ifs <;> (try (exfalso; omega)) <;> norm_num

lemma restrictedSimplex_convex (N : ℕ) : Convex ℝ (restrictedSimplex N) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_stdSimplex ℝ (Fin N) hx.1 hy.1 ha hb hab, ?_⟩
  intro i k hik
  have h1 := hx.2 hik
  have h2 := hy.2 hik
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end RiskUncSets.Symmetric.D6d844d3Aux

open RiskUncSets.Symmetric.D6d844d3Aux in
open RiskUncSets.Symmetric in
theorem solution {N : ℕ} (hN : 0 < N)
    (lam : Fin (Nhat N) → ℝ) (h0 : ∀ j, 0 ≤ lam j)
    (h1 : ∑ j, lam j = 1) :
    (∑ j, lam j • qbar j) ∈ restrictedSimplex N := by
  exact (restrictedSimplex_convex N).sum_mem (fun j _ => h0 j) h1
    (fun j _ => qbar_mem hN j)
