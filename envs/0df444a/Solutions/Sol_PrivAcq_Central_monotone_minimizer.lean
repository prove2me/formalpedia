-- Prove2me | solution 1 for PrivAcq.Central.monotone_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:11:11.244824+00:00
-- url     : https://prove2.me/submissions/276c92bc-ce4c-4a3f-8492-dac09e69649b

import Mathlib
import Definitions.Def_PrivAcq_Central_Model

open PrivAcq.Central in
theorem solution {n : ℕ} (S : Setting n) (hA1 : S.Assumption1)
    (c c' y y' : Fin n → ℝ) (hc : c ∈ S.types) (hc' : c' ∈ S.types) (i : Fin n)
    (hcc' : ∀ j : Fin n, j ≠ i → c j = c' j)
    (hy : IsOpt23 S c y) (hy' : IsOpt23 S c' y') :
    (y i - y' i) * (S.ψ i (c i) - S.ψ i (c' i)) ≤ 0 ∧ (c i < c' i → y' i ≤ y i) := by
  have h1 := hy.2 y' hy'.1
  have h2 := hy'.2 y hy.1
  unfold obj23 at h1 h2
  have expand : ∑ j, (S.ψ j (c j) - S.ψ j (c' j)) * (y j - y' j) =
      (∑ j, S.ψ j (c j) * y j) - (∑ j, S.ψ j (c j) * y' j)
        - (∑ j, S.ψ j (c' j) * y j) + (∑ j, S.ψ j (c' j) * y' j) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have single : ∑ j, (S.ψ j (c j) - S.ψ j (c' j)) * (y j - y' j) =
      (S.ψ i (c i) - S.ψ i (c' i)) * (y i - y' i) := by
    apply Finset.sum_eq_single i
    · intro j _ hj
      rw [hcc' j hj, sub_self, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : (y i - y' i) * (S.ψ i (c i) - S.ψ i (c' i)) ≤ 0 := by
    rw [mul_comm, ← single, expand]
    linarith
  refine ⟨key, fun hlt => ?_⟩
  have hci : c i ∈ Set.Icc (S.a i) (S.b i) := hc i (Set.mem_univ i)
  have hci' : c' i ∈ Set.Icc (S.a i) (S.b i) := hc' i (Set.mem_univ i)
  have hψ : S.ψ i (c i) < S.ψ i (c' i) := hA1 i hci hci' hlt
  by_contra hne
  push_neg at hne
  have : 0 < (y i - y' i) * (S.ψ i (c i) - S.ψ i (c' i)) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith
