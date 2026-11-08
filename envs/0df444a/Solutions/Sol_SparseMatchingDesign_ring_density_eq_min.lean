-- Prove2me | solution 1 for SparseMatchingDesign.ring_density_eq_min
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:07:41.321102+00:00
-- url     : https://prove2.me/submissions/d32ff9a5-c464-4a77-b8d9-ab3fc5dac752

import Mathlib
import Definitions.Def_SparseMatchingDesign_kRing
import Definitions.Def_SparseMatchingDesign_density

namespace Aux_SMD_ring
open SparseMatchingDesign

def R (c cv a : ℕ) : Prop :=
  |(a : ℤ) - cv| ≤ 1 ∨ (cv = 0 ∧ a + 1 = c) ∨ (a = 0 ∧ cv + 1 = c)

instance (c cv a : ℕ) : Decidable (R c cv a) := by unfold R; infer_instance

theorem R_iff (c cv a : ℕ) : R c cv a ↔
    (a ≤ cv + 1 ∧ cv ≤ a + 1) ∨ (cv = 0 ∧ a + 1 = c) ∨ (a = 0 ∧ cv + 1 = c) := by
  unfold R; rw [abs_le]; constructor <;> rintro (h | h | h) <;> first
    | (left; constructor <;> omega) | (right; left; exact h) | (right; right; exact h)

theorem countN (c cv : ℕ) (hc : 0 < c) (hcv : cv < c) :
    ((Finset.univ : Finset (Fin c)).filter (fun a => R c cv a.val)).card = min 3 c := by
  have key : ∀ S : Finset ℕ, (∀ a, a ∈ S ↔ a < c ∧ R c cv a) →
      ((Finset.univ : Finset (Fin c)).filter (fun a => R c cv a.val)).card = S.card := by
    intro S hS
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha; rw [hS]; exact ⟨a.2, (Finset.mem_filter.mp ha).2⟩
    · intro a _ b _ h; exact Fin.ext h
    · intro b hb
      rw [hS] at hb
      exact ⟨⟨b, hb.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2⟩, rfl⟩
  by_cases h3 : c ≤ 3
  · rw [key (Finset.range c), Finset.card_range, min_eq_right h3]
    intro a; rw [Finset.mem_range, R_iff]; constructor
    · intro ha; refine ⟨ha, ?_⟩; omega
    · exact fun h => h.1
  · push_neg at h3
    rw [min_eq_left h3.le]
    by_cases h0 : cv = 0
    · subst h0
      rw [key {0, 1, c - 1}]
      · rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
      · intro a
        simp only [Finset.mem_insert, Finset.mem_singleton]
        unfold R; rw [abs_le]
        constructor <;> intro h <;> omega
    · by_cases hl : cv + 1 = c
      · rw [key {0, cv - 1, cv}]
        · rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
        · intro a
          simp only [Finset.mem_insert, Finset.mem_singleton]
          unfold R; rw [abs_le]
          constructor <;> intro h <;> omega
      · rw [key {cv - 1, cv, cv + 1}]
        · rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
        · intro a
          simp only [Finset.mem_insert, Finset.mem_singleton]
          unfold R; rw [abs_le]
          constructor <;> intro h <;> omega

theorem adj_iff (n K : ℕ) (v j : Fin n) :
    (kRing n K).Adj v j ↔ v ≠ j ∧ R (n / K) (v.val / K) (j.val / K) := by
  show (v ≠ j ∧ _) ↔ _
  unfold R cluster
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩

theorem countR (K c : ℕ) (hK : 0 < K) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin (K * c))).filter (fun j => P (j.val / K))).card =
      ((Finset.univ : Finset (Fin c)).filter (fun a => P a.val)).card * K := by
  conv_rhs => rw [← Fintype.card_fin K, ← Finset.card_univ]
  rw [← Finset.card_product]
  symm
  apply Finset.card_bij (fun (p : Fin c × Fin K) _ => (⟨p.2.val + K * p.1.val, by
      have := p.1.2; have := p.2.2; nlinarith⟩ : Fin (K * c)))
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    rwa [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt b.2, zero_add]
  · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    simp only [Fin.mk.injEq] at h
    have h1 : (b.val + K * a.val) / K = (b'.val + K * a'.val) / K := by rw [h]
    rw [Nat.add_mul_div_left _ _ hK, Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt b.2,
      Nat.div_eq_of_lt b'.2] at h1
    have h2 : (b.val + K * a.val) % K = (b'.val + K * a'.val) % K := by rw [h]
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.2,
      Nat.mod_eq_of_lt b'.2] at h2
    simp only [zero_add] at h1
    ext <;> simp [Fin.ext_iff] <;> omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hjc : j.val / K < c := by
      rw [Nat.div_lt_iff_lt_mul hK]; have := j.2; linarith [mul_comm K c]
    refine ⟨(⟨j.val / K, hjc⟩, ⟨j.val % K, Nat.mod_lt _ hK⟩), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact hj
    · apply Fin.ext; simp only; exact Nat.mod_add_div j.val K

end Aux_SMD_ring

open SparseMatchingDesign Aux_SMD_ring in
theorem solution (n K : ℕ) (hK : 0 < K) (hKn : K ∣ n) (hn : 0 < n) :
    (∀ v : Fin n, ((kRing n K).neighborSet v).ncard = min (3 * K - 1) (n - 1)) ∧
    density (kRing n K) = ((min (3 * K - 1) (n - 1) : ℕ) : ℝ) := by
  classical
  obtain ⟨c, rfl⟩ := hKn
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; simp at hn
    · exact h
  have hdiv : K * c / K = c := Nat.mul_div_cancel_left c hK
  have hnb : ∀ v : Fin (K * c), ((kRing (K * c) K).neighborSet v).ncard = min (3 * K - 1) (K * c - 1) := by
    intro v
    have hvc : v.val / K < c := by
      rw [Nat.div_lt_iff_lt_mul hK]; have := v.2; linarith [mul_comm K c]
    rw [Set.ncard_eq_toFinset_card']
    have hset : ((kRing (K * c) K).neighborSet v).toFinset =
        ((Finset.univ : Finset (Fin (K * c))).filter (fun j => R c (v.val / K) (j.val / K))).erase v := by
      ext j
      simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet, adj_iff, hdiv, Finset.mem_erase,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, h2⟩
    rw [hset, Finset.card_erase_of_mem, countR K c hK (fun a => R c (v.val / K) a),
      countN c _ hc hvc]
    · rcases le_or_gt c 3 with h3 | h3
      · rw [min_eq_right h3]
        have : K * c ≤ 3 * K := by nlinarith
        rw [min_eq_right (by omega)]
        rw [mul_comm]
      · rw [min_eq_left h3.le]
        have : 3 * K ≤ K * c := by nlinarith
        rw [min_eq_left (by omega)]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold R; left; simp
  refine ⟨hnb, ?_⟩
  unfold density
  simp only [hnb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp
