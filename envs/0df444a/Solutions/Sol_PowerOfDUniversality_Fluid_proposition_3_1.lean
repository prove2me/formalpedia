-- Prove2me | solution 1 for PowerOfDUniversality.Fluid.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:43:23.665322+00:00
-- url     : https://prove2.me/submissions/bab85ba7-6f40-4117-95eb-7b306e4ed2bb

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid.Prop31Aux

open PowerOfDUniversality.Fluid

lemma tailSum_eq_sum (Q : ℕ →₀ ℕ) (m : ℕ) :
    tailSum Q m = Q.sum (fun i a => if m ≤ i then a else 0) := by
  unfold tailSum Finsupp.sum
  rw [Finset.sum_filter]

lemma tailSum_add (Q R : ℕ →₀ ℕ) (m : ℕ) :
    tailSum (Q + R) m = tailSum Q m + tailSum R m := by
  simp only [tailSum_eq_sum]
  rw [Finsupp.sum_add_index']
  · intro i; simp
  · intro i a b; split_ifs <;> simp

lemma tailSum_single (j m : ℕ) :
    tailSum (Finsupp.single j 1) m = if m ≤ j then 1 else 0 := by
  rw [tailSum_eq_sum, Finsupp.sum_single_index]; simp

lemma tailSum_succ (Q : ℕ →₀ ℕ) (m : ℕ) : tailSum Q m = Q m + tailSum Q (m + 1) := by
  simp only [tailSum_eq_sum]
  have h : (fun i a => if m ≤ i then a else 0) =
      (fun (i : ℕ) (a : ℕ) => (if i = m then a else 0) + (if m + 1 ≤ i then a else 0)) := by
    funext i a; split_ifs <;> omega
  rw [h, Finsupp.sum_add, Finsupp.sum_ite_eq']
  by_cases hm : m ∈ Q.support
  · simp [hm]
  · simp only [hm, if_false]
    rw [Finsupp.notMem_support_iff] at hm
    simp [hm]

lemma tailSum_sub_single (Q : ℕ →₀ ℕ) (j m : ℕ) (hj : 1 ≤ Q j) :
    tailSum (Q - Finsupp.single j 1) m + (if m ≤ j then 1 else 0) = tailSum Q m := by
  have hle : Finsupp.single j 1 ≤ Q := by
    rw [Finsupp.single_le_iff]; exact hj
  have hQ : Q = (Q - Finsupp.single j 1) + Finsupp.single j 1 :=
    (tsub_add_cancel_of_le hle).symm
  conv_rhs => rw [hQ]
  rw [tailSum_add, tailSum_single]

lemma tailSum_eq_zero (N : ℕ) (b : ℕ∞) (Q : ℕ →₀ ℕ) (hQ : IsOccupancy N b Q) (m : ℕ)
    (hm : b < (m : ℕ∞)) : tailSum Q m = 0 := by
  unfold tailSum
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  apply hQ.2.2 i
  exact lt_of_lt_of_le hm (by exact_mod_cast hi.2)

lemma le_level_iff (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (Q : ℕ →₀ ℕ) (hQ : IsOccupancy N b Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) (i : ℕ) :
    i ≤ level N Q c ↔ N + 1 ≤ Q i + c := by
  obtain ⟨h0, hanti, _⟩ := hQ
  constructor
  · intro hi
    have hne : (Q.support.filter (fun i => N + 1 ≤ Q i + c)).Nonempty := by
      refine ⟨0, ?_⟩
      rw [Finset.mem_filter, Finsupp.mem_support_iff, h0]
      omega
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [Finset.mem_filter] at hj
    have hl : level N Q c = j := hjeq
    have := hanti (show i ≤ j by omega)
    omega
  · intro hi
    apply Finset.le_sup (f := id)
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨by omega, hi⟩

lemma level_le_b (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (Q : ℕ →₀ ℕ) (hQ : IsOccupancy N b Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) : ((level N Q c : ℕ) : ℕ∞) ≤ b := by
  by_contra h
  push Not at h
  have h1 := (le_level_iff N hN b Q hQ c hc1 hcN (level N Q c)).mp le_rfl
  have h2 := hQ.2.2 _ h
  omega

lemma remove_key (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (X : Ensemble) (hX : IsOccupancy N b X.Q)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (m : ℕ) (hm : 1 ≤ m) :
    tailSum (removeItem N k X).Q m + (removeItem N k X).L
      + (if m ≤ level N X.Q k then 1 else 0) = tailSum X.Q m + X.L := by
  unfold removeItem
  split_ifs with h1 h2 h2
  · have hj := (le_level_iff N hN b X.Q hX k hk1 hkN (level N X.Q k)).mp le_rfl
    have := tailSum_sub_single X.Q (level N X.Q k) m (by omega)
    rw [if_pos h2] at this
    simp only
    omega
  · have hj := (le_level_iff N hN b X.Q hX k hk1 hkN (level N X.Q k)).mp le_rfl
    have := tailSum_sub_single X.Q (level N X.Q k) m (by omega)
    rw [if_neg h2] at this
    simp only
    omega
  · omega
  · simp

lemma add_key (N : ℕ) (b : ℕ∞) (X : Ensemble) (c m : ℕ) :
    tailSum (addItem N b c X).Q m + (addItem N b c X).L =
      tailSum X.Q m + X.L + (if ((level N X.Q c : ℕ) : ℕ∞) < b then
        (if m ≤ level N X.Q c + 1 then 1 else 0) else 1) := by
  unfold addItem
  by_cases h1 : ((level N X.Q c : ℕ) : ℕ∞) < b
  · rw [if_pos h1, if_pos h1]
    simp only [tailSum_add, tailSum_single]; ring
  · rw [if_neg h1, if_neg h1]
    simp only
    omega

end PowerOfDUniversality.Fluid.Prop31Aux

open PowerOfDUniversality.Fluid PowerOfDUniversality.Fluid.Prop31Aux

theorem solution (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (A B : Ensemble)
    (hA : IsOccupancy N b A.Q) (hB : IsOccupancy N b B.Q) (hAB : StackOrdered A B) :
    (∀ k : ℕ, 1 ≤ k → k ≤ N → StackOrdered (removeItem N k A) (removeItem N k B)) ∧
    (∀ nA nB : ℕ, 1 ≤ nA → nA ≤ nB → nB ≤ N →
      StackOrdered (addItem N b nA A) (addItem N b nB B)) := by
  constructor
  · intro k hk1 hkN m hm
    have kA := remove_key N hN b A hA k hk1 hkN m hm
    have kB := remove_key N hN b B hB k hk1 hkN m hm
    have h1 := hAB m hm
    have h2 := hAB (m + 1) (by omega)
    have sA := tailSum_succ A.Q m
    have sB := tailSum_succ B.Q m
    have lA := le_level_iff N hN b A.Q hA k hk1 hkN m
    have lB := le_level_iff N hN b B.Q hB k hk1 hkN m
    split_ifs at kA kB with c1 c2 c2
    · omega
    · have := lA.mp c1
      have : ¬ N + 1 ≤ B.Q m + k := fun h => c2 (lB.mpr h)
      omega
    · have : ¬ N + 1 ≤ A.Q m + k := fun h => c1 (lA.mpr h)
      have := lB.mp c2
      omega
    · omega
  · intro nA nB hnA hAB' hnB m hm
    have kA := add_key N b A nA m
    have kB := add_key N b B nB m
    show tailSum (addItem N b nA A).Q m + (addItem N b nA A).L ≤
      tailSum (addItem N b nB B).Q m + (addItem N b nB B).L
    rw [kA, kB]
    have h1 := hAB m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rcases Nat.eq_zero_or_pos m' with hm0 | hm0
    · subst hm0
      split_ifs <;> omega
    have h0 := hAB m' hm0
    have sA := tailSum_succ A.Q m'
    have sB := tailSum_succ B.Q m'
    have lA := le_level_iff N hN b A.Q hA nA hnA (by omega) m'
    have lB := le_level_iff N hN b B.Q hB nB (by omega) hnB m'
    -- the only nontrivial case: A increases, B does not
    by_cases hBinc : (if ((level N B.Q nB : ℕ) : ℕ∞) < b then
        (if m' + 1 ≤ level N B.Q nB + 1 then 1 else 0) else 1) = 1
    · rw [hBinc]; split_ifs <;> omega
    have hBlt : ((level N B.Q nB : ℕ) : ℕ∞) < b := by
      by_contra h; rw [if_neg h] at hBinc; exact hBinc rfl
    rw [if_pos hBlt] at hBinc
    have hBm : ¬ m' + 1 ≤ level N B.Q nB + 1 := by
      intro h; rw [if_pos h] at hBinc; exact hBinc rfl
    rw [if_pos hBlt, if_neg hBm]
    have hQB : ¬ N + 1 ≤ B.Q m' + nB := fun h => hBm (by have := lB.mpr h; omega)
    by_cases hmA : m' ≤ level N A.Q nA
    · have := lA.mp hmA
      split_ifs <;> omega
    · -- then A must discard to increase
      by_cases hAlt : ((level N A.Q nA : ℕ) : ℕ∞) < b
      · rw [if_pos hAlt, if_neg (by omega)]; omega
      rw [if_neg hAlt]
      have hbne : b ≠ ⊤ := by
        intro h; rw [h] at hAlt; exact hAlt (ENat.natCast_lt_top _)
      obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hbne
      have hlA := level_le_b N hN (n : ℕ∞) A.Q hA nA hnA (by omega)
      have hlA' : level N A.Q nA ≤ n := by exact_mod_cast hlA
      have hlA'' : n ≤ level N A.Q nA := by
        push Not at hAlt; exact_mod_cast hAlt
      have hlB' : level N B.Q nB < n := by exact_mod_cast hBlt
      have hn1 : 1 ≤ n := by exact_mod_cast hb
      have hn := hAB n hn1
      have tA := tailSum_succ A.Q n
      have tB := tailSum_succ B.Q n
      have zA := tailSum_eq_zero N (n : ℕ∞) A.Q hA (n + 1) (by exact_mod_cast (by omega : n < n + 1))
      have zB := tailSum_eq_zero N (n : ℕ∞) B.Q hB (n + 1) (by exact_mod_cast (by omega : n < n + 1))
      have zA' := tailSum_eq_zero N (n : ℕ∞) A.Q hA (m' + 1) (by exact_mod_cast (by omega : n < m' + 1))
      have zB' := tailSum_eq_zero N (n : ℕ∞) B.Q hB (m' + 1) (by exact_mod_cast (by omega : n < m' + 1))
      have cA := (le_level_iff N hN (n : ℕ∞) A.Q hA nA hnA (by omega) n).mp hlA''
      have cB : ¬ N + 1 ≤ B.Q n + nB := fun h =>
        absurd ((le_level_iff N hN (n : ℕ∞) B.Q hB nB (by omega) (by omega) n).mpr h) (by omega)
      omega
