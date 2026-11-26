-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.tsum_evenUSummand_eq_normalized_U
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:14.798801+00:00
-- url     : https://prove2.me/submissions/5a219812-4b6b-4349-8126-d4ec9d83426a

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private theorem centered_power_normalization {p a j : ℕ} (hp : 1 ≤ p) (hj : j ≤ a) :
    (p : ℝ)⁻¹ ^ (a * a) * (p : ℝ) ^ ((a + j) * (a - j)) =
      (p : ℝ)⁻¹ ^ (j * j) := by
  have hexp : a * a = j * j + (a + j) * (a - j) := by
    have := Nat.sub_add_cancel hj
    nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [hexp, pow_add]
  simp [inv_pow, hp0]
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, evenUSummand p a j =
      (p : ℝ)⁻¹ ^ (a * a) * primePowerU p (2 * a) := by
  let f : ℕ → ℝ := fun r ↦
    (p : ℝ)⁻¹ ^ (a * a) *
      ((p : ℝ) ^ (r * (2 * a - r)) * (gammaR (p : ℝ) r)⁻¹)
  have hhigh (j : ℕ) (hj : j < a) :
      f (a + (j + 1)) = (p : ℝ)⁻¹ ^ ((j + 1) * (j + 1)) *
        (gammaR (p : ℝ) (a + (j + 1)))⁻¹ := by
    have hja : j + 1 ≤ a := by omega
    dsimp [f]
    have hsub : 2 * a - (a + (j + 1)) = a - (j + 1) := by omega
    rw [hsub, ← mul_assoc, centered_power_normalization (by omega) hja]
  have hlow (j : ℕ) (hj : j < a) :
      f (a - 1 - j) = (p : ℝ)⁻¹ ^ ((j + 1) * (j + 1)) *
        (gammaR (p : ℝ) (a - (j + 1)))⁻¹ := by
    have hja : j + 1 ≤ a := by omega
    have hindex : a - 1 - j = a - (j + 1) := by omega
    have hsub : 2 * a - (a - (j + 1)) = a + (j + 1) := by omega
    dsimp [f]
    rw [hindex, hsub]
    have hcenter := centered_power_normalization (p := p) (a := a) (j := j + 1)
      (by omega) hja
    rw [mul_comm (a - (j + 1)) (a + (j + 1)), ← mul_assoc, hcenter]
  rw [tsum_eq_sum (s := Finset.range (a + 1))]
  · rw [Finset.sum_range_succ']
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hcenter : f a = (gammaR (p : ℝ) a)⁻¹ := by
      dsimp [f]
      have hsub : 2 * a - a = a := by omega
      rw [hsub]
      simp [inv_pow, hp0]
    have hpairs : (∑ j ∈ Finset.range a, evenUSummand p a (j + 1)) =
        (∑ r ∈ Finset.range a, f r) +
          ∑ j ∈ Finset.range a, f (a + 1 + j) := by
      rw [← Finset.sum_range_reflect f a, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j < a := Finset.mem_range.mp hj
      have hind : a + 1 + j = a + (j + 1) := by omega
      rw [hind, hhigh j hja, hlow j hja]
      simp [evenUSummand, show j + 1 ≤ a by omega]
      ring
    rw [hpairs]
    simp only [evenUSummand, if_pos]
    rw [← hcenter]
    have hU : (p : ℝ)⁻¹ ^ (a * a) * primePowerU p (2 * a) =
        ∑ r ∈ Finset.range (2 * a + 1), f r := by
      rw [primePowerU]
      have hfin := Fin.sum_univ_eq_sum_range
        (fun r : ℕ ↦ (p : ℝ) ^ (r * (2 * a - r)) *
          (gammaR (p : ℝ) r)⁻¹) (2 * a + 1)
      rw [hfin, Finset.mul_sum]
    rw [hU]
    have hsize : 2 * a + 1 = (a + 1) + a := by omega
    rw [hsize, Finset.sum_range_add, Finset.sum_range_succ]
    ring
  · intro j hj
    have hja : a < j := by
      rw [Finset.mem_range, not_lt] at hj
      omega
    simp [evenUSummand, show j ≠ 0 by omega, show ¬j ≤ a by omega]
end SharpIntermediateSubgroupBounds
