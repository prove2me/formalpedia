-- Prove2me | solution 1 for QMaxCutSDP.Rounding.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T23:01:50.509518+00:00
-- url     : https://prove2.me/submissions/0e5eedc2-5c17-48fb-bc15-44a7f6241a1f

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Model

open Matrix MeasureTheory
open QMaxCutSDP.Rounding

namespace QSDPl4Aux

lemma nn {N : ℕ} (x : Fin N → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg _

lemma selfE {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v) (p q : Fin n) (hpq : p ≠ q) :
    vEdge v p q ⬝ᵥ vEdge v p q = 3 - 2 * (vEdge v p q ⬝ᵥ v.v0) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  simp only [vEdge, Fin.sum_univ_three, add_dotProduct, dotProduct_add]
  rw [h3 p q 0 hpq, h3 p q 1 hpq, h3 p q 2 hpq,
    h7 p q 0 1 2 hpq (by decide) (by decide) (by decide),
    h7 p q 0 2 1 hpq (by decide) (by decide) (by decide),
    h7 p q 1 0 2 hpq (by decide) (by decide) (by decide),
    h7 p q 1 2 0 hpq (by decide) (by decide) (by decide),
    h7 p q 2 0 1 hpq (by decide) (by decide) (by decide),
    h7 p q 2 1 0 hpq (by decide) (by decide) (by decide)]
  ring

lemma Sle1 {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v) (p q : Fin n) (hpq : p ≠ q) :
    vEdge v p q ⬝ᵥ v.v0 ≤ 1 := by
  have h := nn (v.v0 - vEdge v p q)
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, selfE v hv p q hpq, hv.1,
    dotProduct_comm v.v0 (vEdge v p q)] at h
  linarith

lemma crossE {n N : ℕ} (v : SDPVec n N) (hv : IsSFeasible v) (i j k : Fin n) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    vEdge v i j ⬝ᵥ vEdge v i k = vEdge v j k ⬝ᵥ v.v0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hv
  simp only [vEdge, Fin.sum_univ_three, add_dotProduct, dotProduct_add]
  rw [h8 i j 0 hij, h8 i j 1 hij, h8 i j 2 hij]
  rw [h5 j i k 0 hij.symm hik hjk, h5 j i k 1 hij.symm hik hjk, h5 j i k 2 hij.symm hik hjk,
    h6 j i k 0 1 hij.symm hik hjk (by decide), h6 j i k 0 2 hij.symm hik hjk (by decide),
    h6 j i k 1 0 hij.symm hik hjk (by decide), h6 j i k 1 2 hij.symm hik hjk (by decide),
    h6 j i k 2 0 hij.symm hik hjk (by decide), h6 j i k 2 1 hij.symm hik hjk (by decide)]
  ring

end QSDPl4Aux

open QSDPl4Aux

theorem solution {n N : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : SDPVec n N) (hv : IsSFeasible v) (i : Fin n)
    (T : Finset (Fin n)) (hi : i ∉ T) (hT : ∀ j ∈ T, G.Adj i j) :
    (1 / 4 : ℝ) * ∑ j ∈ T, ((v.v0 - vEdge v i j) ⬝ᵥ v.v0) ≤
      ((T.card : ℝ) + 1) / 2 := by
  have hne : ∀ j ∈ T, i ≠ j := fun j hj h => hi (h ▸ hj)
  set A := ∑ j ∈ T, vEdge v i j ⬝ᵥ v.v0 with hA
  set U := ∑ j ∈ T, vEdge v i j with hU
  have hUv : U ⬝ᵥ v.v0 = A := by rw [hU, sum_dotProduct]
  have hUU : U ⬝ᵥ U ≤ 3 * T.card - 2 * A + (T.card : ℝ) * (T.card - 1) := by
    rw [hU, sum_dotProduct]
    simp only [dotProduct_sum]
    have : ∀ j ∈ T, ∑ k ∈ T, vEdge v i j ⬝ᵥ vEdge v i k ≤
        3 - 2 * (vEdge v i j ⬝ᵥ v.v0) + ((T.card : ℝ) - 1) := by
      intro j hj
      rw [← Finset.add_sum_erase T _ hj, selfE v hv i j (hne j hj)]
      have h2 : ∑ k ∈ T.erase j, vEdge v i j ⬝ᵥ vEdge v i k ≤ ∑ k ∈ T.erase j, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkj : k ≠ j := Finset.ne_of_mem_erase hk
        have hkT : k ∈ T := Finset.mem_of_mem_erase hk
        rw [crossE v hv i j k (hne j hj) (hne k hkT) hkj.symm]
        exact Sle1 v hv j k hkj.symm
      rw [Finset.sum_const, Finset.card_erase_of_mem hj, nsmul_eq_mul, mul_one,
        Nat.cast_sub (Finset.card_pos.2 ⟨j, hj⟩), Nat.cast_one] at h2
      linarith
    calc ∑ j ∈ T, ∑ k ∈ T, vEdge v i j ⬝ᵥ vEdge v i k
        ≤ ∑ j ∈ T, (3 - 2 * (vEdge v i j ⬝ᵥ v.v0) + ((T.card : ℝ) - 1)) :=
          Finset.sum_le_sum this
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hA]
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
  have hCS : A ^ 2 ≤ U ⬝ᵥ U := by
    have h := nn (U - A • v.v0)
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      dotProduct_smul, smul_dotProduct, hv.1, hUv, dotProduct_comm v.v0 U, hUv] at h
    simp only [smul_eq_mul] at h
    nlinarith
  have hgoal : ∑ j ∈ T, ((v.v0 - vEdge v i j) ⬝ᵥ v.v0) = T.card - A := by
    rw [hA]
    simp only [sub_dotProduct, hv.1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_one]
  rw [hgoal]
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  nlinarith
