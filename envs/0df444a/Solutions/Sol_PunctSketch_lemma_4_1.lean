-- Prove2me | solution 1 for PunctSketch.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:01:25.813966+00:00
-- url     : https://prove2.me/submissions/aed4dc4c-7a67-4eef-a684-a80cbe697808

import Mathlib
import Definitions.Def_PunctSketch_sketch
import Definitions.Def_PunctSketch_puncture

open Classical in
open PunctSketch Polynomial in
theorem solution {n Q : ℕ} [Fact Q.Prime] (α : Fin n → ZMod Q) (G : SimpleGraph (Fin n))
    (F : Finset (Fin n)) (d k : ℕ) (hF : F.card < k) (v : Fin n) (hv : v ∉ F) (t : ℕ)
    (ht : t + F.card < 2 * d + k) :
    puncture α F (sketch G α v) v t =
      ∑ u ∈ Finset.univ.filter (fun u => G.Adj v u ∧ u ∉ F),
        ((sgn u v : ℤ) : ZMod Q) * (α v * α u) ^ t * (puncturePoly α F).eval (α v) *
          (puncturePoly α F).eval (α u) := by
  have hdeg : (puncturePoly α F).natDegree < F.card + 1 := by
    have h1 : (puncturePoly α F).natDegree ≤ ∑ z ∈ F, (X - C (α z)).natDegree := by
      unfold puncturePoly; exact natDegree_prod_le _ _
    have h2 : ∑ z ∈ F, (X - C (α z)).natDegree ≤ ∑ z ∈ F, 1 :=
      Finset.sum_le_sum (fun z _ => natDegree_X_sub_C_le _)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h2
    omega
  have heval : ∀ x, (puncturePoly α F).eval x =
      ∑ i ∈ Finset.range (F.card + 1), (puncturePoly α F).coeff i * x ^ i :=
    fun x => eval_eq_sum_range' hdeg x
  have hzero : ∀ u ∈ F, (puncturePoly α F).eval (α u) = 0 := by
    intro u hu
    unfold puncturePoly
    rw [eval_prod]
    exact Finset.prod_eq_zero hu (by simp)
  have hmain : ∑ i ∈ Finset.range (F.card + 1), (puncturePoly α F).coeff i *
        sketch G α v (t + i) =
      ∑ u, ((signedAdj G v u : ℤ) : ZMod Q) * α u ^ t * (puncturePoly α F).eval (α u) := by
    unfold sketch
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [heval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
    ring
  unfold puncture
  rw [hmain, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  unfold signedAdj
  by_cases hA : G.Adj v u
  · by_cases hu : u ∈ F
    · rw [hzero u hu]; simp
    · rw [if_pos hA, if_pos ⟨hA, hu⟩, mul_pow]; ring
  · rw [if_neg hA, if_neg (fun h => hA h.1)]; simp
