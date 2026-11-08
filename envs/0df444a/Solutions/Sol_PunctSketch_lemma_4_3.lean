-- Prove2me | solution 1 for PunctSketch.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:11:19.351717+00:00
-- url     : https://prove2.me/submissions/570c3af3-3e6a-4c6e-a162-d90298b514b9

import Mathlib
import Definitions.Def_PunctSketch_fingerprint
import Definitions.Def_PunctSketch_puncture

open Classical in
open PunctSketch in
theorem solution {n Q : ℕ} [Fact Q.Prime] (α : Fin n → ZMod Q) (r : Sym2 (Fin n) → ZMod Q)
    (G : SimpleGraph (Fin n)) (F : Finset (Fin n)) (c k : ℕ) (hF : F.card < k) (v : Fin n)
    (hv : v ∉ F) (t : ℕ) (ht : t + F.card < c + k) :
    puncture α F (fingerprint G α r v) v t =
      ∑ u ∈ Finset.univ.filter (fun u => G.Adj v u ∧ u ∉ F),
        ((sgn v u : ℤ) : ZMod Q) * r s(v, u) * (α v * α u) ^ t * (puncturePoly α F).eval (α v) *
          (puncturePoly α F).eval (α u) := by
  have hdeg : (puncturePoly α F).natDegree = F.card := by
    unfold puncturePoly
    exact Polynomial.natDegree_finsetProd_X_sub_C_eq_card F α
  have h1 : ∀ x, (puncturePoly α F).eval x =
      ∑ i ∈ Finset.range (F.card + 1), (puncturePoly α F).coeff i * x ^ i := by
    intro x
    rw [Polynomial.eval_eq_sum_range, hdeg]
  have hz : ∀ u ∈ F, (puncturePoly α F).eval (α u) = 0 := by
    intro u hu
    unfold puncturePoly
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hu (by simp)
  calc puncture α F (fingerprint G α r v) v t
      = ∑ u ∈ Finset.univ.filter (G.Adj v),
        ((sgn v u : ℤ) : ZMod Q) * r s(v, u) * (α v * α u) ^ t * (puncturePoly α F).eval (α v) *
          (puncturePoly α F).eval (α u) := by
        unfold puncture fingerprint
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [h1 (α u), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = _ := by
        symm
        apply Finset.sum_subset
        · intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
          exact hu.1
        · intro u hu hnot
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hu hnot
          rw [hz u (hnot hu), mul_zero]
