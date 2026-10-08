-- Prove2me | solution 1 for QueueingFundamentals.Networks.buzen_recursion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:28:12.424115+00:00
-- url     : https://prove2.me/submissions/8517803a-e547-442a-930b-99c746dc104e

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson



namespace QueueingFundamentals.Networks
open Finset

lemma mem_states_iff' {k N : ℕ} (n : Fin k → ℕ) : n ∈ states k N ↔ ∑ i, n i = N := by
  constructor
  · intro h; exact (Finset.mem_filter.1 h).2
  · intro h
    refine Finset.mem_filter.2 ⟨?_, h⟩
    rw [Fintype.mem_piFinset]; intro i; rw [Finset.mem_range]
    have := Finset.single_le_sum (f := n) (fun j _ => Nat.zero_le _) (Finset.mem_univ i); omega

lemma fiber_sum (m n i : ℕ) (hi : i ≤ n) (F : (Fin (m + 1) → ℕ) → ℝ) :
    ∑ x ∈ (states (m + 1) n).filter (fun x => x (Fin.last m) = i), F x =
      ∑ y ∈ states m (n - i), F (Fin.snoc (α := fun _ => ℕ) y i) := by
  symm
  refine Finset.sum_nbij' (fun y => Fin.snoc (α := fun _ => ℕ) y i) (fun x => Fin.init x)
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [mem_states_iff'] at hy
    refine Finset.mem_filter.2 ⟨?_, by simp⟩
    rw [mem_states_iff', Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hy]; omega
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    rw [mem_states_iff', Fin.sum_univ_castSucc] at hx1
    rw [mem_states_iff']
    simp only [Fin.init]
    omega
  · intro y _; exact Fin.init_snoc _ _
  · intro x hx
    have hx2 := (Finset.mem_filter.1 hx).2
    rw [← hx2]; exact Fin.snoc_init_self x
  · intro y _; rfl

theorem buzen_recursion_core {k : ℕ} (rho : Fin k → ℝ) (c : Fin k → ℕ) (hc : ∀ i, 1 ≤ c i) :
    (∀ N : ℕ, normConst (buzenFactor rho c) N = gBuzen (buzenFactor rho c) k le_rfl N) ∧
    (∀ (m : ℕ) (hm : m + 1 ≤ k) (n : ℕ),
      gBuzen (buzenFactor rho c) (m + 1) hm n =
        ∑ i ∈ range (n + 1),
          buzenFactor rho c ⟨m, hm⟩ i * gBuzen (buzenFactor rho c) m (Nat.le_of_succ_le hm) (n - i)) ∧
    (∀ (h1 : 1 ≤ k) (n : ℕ), gBuzen (buzenFactor rho c) 1 h1 n = buzenFactor rho c ⟨0, h1⟩ n) ∧
    (∀ (m : ℕ) (hm : m ≤ k), gBuzen (buzenFactor rho c) m hm 0 = 1) := by
  set f := buzenFactor rho c with hf
  have hrec : ∀ (m : ℕ) (hm : m + 1 ≤ k) (n : ℕ),
      gBuzen f (m + 1) hm n =
        ∑ i ∈ range (n + 1), f ⟨m, hm⟩ i * gBuzen f m (Nat.le_of_succ_le hm) (n - i) := by
    intro m hm n
    unfold gBuzen
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : Fin (m + 1) → ℕ => x (Fin.last m))
      (t := range (n + 1))]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [fiber_sum m n i hi', Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [mul_comm]; rfl
    · intro x hx
      rw [mem_states_iff'] at hx
      rw [Finset.mem_range]
      have := Finset.single_le_sum (f := x) (fun j _ => Nat.zero_le _) (Finset.mem_univ (Fin.last m))
      omega
  have g0 : ∀ (h0 : 0 ≤ k) (j : ℕ), gBuzen f 0 h0 j = if j = 0 then 1 else 0 := by
    intro h0 j
    unfold gBuzen
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_const, nsmul_eq_mul, mul_one]
    split_ifs with hj
    · subst hj
      have : states 0 0 = {Fin.elim0} := by
        ext x; rw [mem_states_iff', Finset.mem_singleton]
        simp only [Finset.univ_eq_empty, Finset.sum_empty, true_iff]
        exact Subsingleton.elim _ _
      rw [this]; simp
    · have : states 0 j = ∅ := by
        ext x; rw [mem_states_iff']; simp; omega
      rw [this]; simp
  refine ⟨?_, hrec, ?_, ?_⟩
  · intro N; rfl
  · intro h1 n
    rw [hrec 0 h1 n, Finset.sum_eq_single n]
    · rw [g0, Nat.sub_self, if_pos rfl, mul_one]
    · intro b hb hbn
      have : b ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      rw [g0, if_neg (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  · intro m hm
    unfold gBuzen
    have : states m 0 = {0} := by
      ext x; rw [mem_states_iff', Finset.mem_singleton]
      constructor
      · intro h; funext i; exact (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_univ i)
      · rintro rfl; simp
    rw [this, Finset.sum_singleton]
    refine Finset.prod_eq_one fun i _ => ?_
    have hci : 0 < c (Fin.castLE hm i) := hc _
    simp [hf, buzenFactor, serverFactor, hci]

theorem last_node_marginal_core {k : ℕ} (rho : Fin (k + 1) → ℝ) (c : Fin (k + 1) → ℕ)
    (N n : ℕ) (hn : n ≤ N) :
    marginal N (productForm (buzenFactor rho c) N) (Fin.last k) n =
      buzenFactor rho c (Fin.last k) n * gBuzen (buzenFactor rho c) k (Nat.le_succ k) (N - n) /
        normConst (buzenFactor rho c) N := by
  unfold marginal gBuzen
  have e : ∀ x ∈ (states (k + 1) N).filter (fun x => x (Fin.last k) = n),
      productForm (buzenFactor rho c) N x =
        (∏ i, buzenFactor rho c i (x i)) / normConst (buzenFactor rho c) N := by
    intro x hx
    rw [productForm, if_pos (Finset.mem_filter.1 hx).1]
  rw [Finset.sum_congr rfl e, ← Finset.sum_div, fiber_sum k N n hn, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [mul_comm]; rfl

end QueueingFundamentals.Networks

open QueueingFundamentals.Networks
open Finset

theorem solution {k : ℕ} (rho : Fin k → ℝ) (c : Fin k → ℕ) (hc : ∀ i, 1 ≤ c i) :
    (∀ N : ℕ, normConst (buzenFactor rho c) N = gBuzen (buzenFactor rho c) k le_rfl N) ∧
    (∀ (m : ℕ) (hm : m + 1 ≤ k) (n : ℕ),
      gBuzen (buzenFactor rho c) (m + 1) hm n =
        ∑ i ∈ range (n + 1),
          buzenFactor rho c ⟨m, hm⟩ i * gBuzen (buzenFactor rho c) m (Nat.le_of_succ_le hm) (n - i)) ∧
    (∀ (h1 : 1 ≤ k) (n : ℕ), gBuzen (buzenFactor rho c) 1 h1 n = buzenFactor rho c ⟨0, h1⟩ n) ∧
    (∀ (m : ℕ) (hm : m ≤ k), gBuzen (buzenFactor rho c) m hm 0 = 1) := by
  exact buzen_recursion_core rho c hc
