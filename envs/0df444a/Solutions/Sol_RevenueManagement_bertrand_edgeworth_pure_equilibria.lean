-- Prove2me | solution 1 for RevenueManagement.bertrand_edgeworth_pure_equilibria
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T21:44:35.661922+00:00
-- url     : https://prove2.me/submissions/dd127c5a-457d-414a-bbe6-65f5d1bf5f02

import Mathlib
import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

open Finset

theorem beSales_of_below_empty {n : ℕ} (a C : ℝ) (p : Fin n → ℝ) (i : Fin n)
    (hbelow : (Finset.univ.filter (fun j => p j < p i)) = ∅) :
    beSales a C p i
      = min C (max 0 (a - p i) / ((Finset.univ.filter (fun j => p j = p i)).card : ℝ)) := by
  rw [beSales.eq_1, hbelow]
  simp

theorem beSales_nonneg {n : ℕ} (a C : ℝ) (hC : 0 < C) (p : Fin n → ℝ) (i : Fin n) :
    0 ≤ beSales a C p i := by
  rw [beSales.eq_1]
  exact le_min hC.le (div_nonneg (le_max_left _ _) (Nat.cast_nonneg _))

theorem beSales_le (a C : ℝ) {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    beSales a C p i ≤ C := by
  rw [beSales.eq_1]; exact min_le_left _ _

-- Case (i): C ≥ (a-c)/(n-1), all firms priced at c.
theorem bertrand_case1 {n : ℕ} (hn : 2 ≤ n) (a c C : ℝ) (hac : c < a) (hC : 0 < C)
    (hCge : (a - c) / (n - 1) ≤ C) :
    IsBEEquilibrium a c C (fun _ : Fin n => c) ∧ ∀ i, bePayoff a c C (fun _ : Fin n => c) i = 0 := by
  have hpayoff0 : ∀ i, bePayoff a c C (fun _ : Fin n => c) i = 0 := by
    intro i; unfold bePayoff; simp
  refine ⟨fun i p' => ?_, hpayoff0⟩
  rw [hpayoff0 i]
  unfold bePayoff
  rw [Function.update_self]
  rcases lt_or_ge c p' with hp' | hp'
  · -- p' > c: firm i is priced strictly above the n-1 rivals, all tied at c.
    have hn1 : 1 ≤ n - 1 := by omega
    have hrival : ∀ j : Fin n, j ≠ i →
        beSales a C (Function.update (fun _ : Fin n => c) i p') j
          = min C (max 0 (a - c) / ((n : ℝ) - 1)) := by
      intro j hj
      have hbelow : (Finset.univ.filter
          (fun k => Function.update (fun _ : Fin n => c) i p' k
            < Function.update (fun _ : Fin n => c) i p' j)) = ∅ := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        rw [Function.update_of_ne hj]
        by_cases hk : k = i
        · subst hk; rw [Function.update_self]; linarith
        · rw [Function.update_of_ne hk]; exact lt_irrefl c
      have htie : (Finset.univ.filter
          (fun k => Function.update (fun _ : Fin n => c) i p' k
            = Function.update (fun _ : Fin n => c) i p' j)) = Finset.univ.erase i := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
        rw [Function.update_of_ne hj]
        by_cases hk : k = i
        · subst hk; simp only [Function.update_self, not_true_eq_false, false_and, iff_false]
          exact hp'.ne'
        · rw [Function.update_of_ne hk]
          simp [hk]
      rw [beSales_of_below_empty a C _ j hbelow, htie, Function.update_of_ne hj,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      have hn1' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        have h1n : 1 ≤ n := by omega
        rw [Nat.cast_sub h1n, Nat.cast_one]
      rw [hn1']
    have hval : ∀ j : Fin n, j ≠ i →
        beSales a C (Function.update (fun _ : Fin n => c) i p') j = (a - c) / ((n:ℝ) - 1) := by
      intro j hj
      rw [hrival j hj, max_eq_right (by linarith : (0:ℝ) ≤ a - c), min_eq_right hCge]
    have hbelowi : (Finset.univ.filter
        (fun k => Function.update (fun _ : Fin n => c) i p' k
          < Function.update (fun _ : Fin n => c) i p' i)) = Finset.univ.erase i := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
      rw [Function.update_self]
      by_cases hk : k = i
      · subst hk; simp
      · rw [Function.update_of_ne hk]; simp [hk, hp']
    have htiei : (Finset.univ.filter
        (fun k => Function.update (fun _ : Fin n => c) i p' k
          = Function.update (fun _ : Fin n => c) i p' i)) = {i} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [Function.update_self]
      by_cases hk : k = i
      · subst hk; simp
      · rw [Function.update_of_ne hk]
        simp only [hk, iff_false]
        exact hp'.ne
    have hsum : (∑ j ∈ (Finset.univ.filter
        (fun k => Function.update (fun _ : Fin n => c) i p' k
          < Function.update (fun _ : Fin n => c) i p' i)).attach,
        beSales a C (Function.update (fun _ : Fin n => c) i p') j.1) = a - c := by
      rw [hbelowi]
      have : ∀ j ∈ (Finset.univ.erase i).attach,
          beSales a C (Function.update (fun _ : Fin n => c) i p') j.1 = (a - c) / ((n:ℝ) - 1) := by
        intro j _
        exact hval j.1 (Finset.ne_of_mem_erase j.2)
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_attach,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      have h1n : 1 ≤ n := by omega
      have hn0 : (n : ℝ) - 1 ≠ 0 := by
        have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        linarith
      rw [nsmul_eq_mul, Nat.cast_sub h1n, Nat.cast_one]
      field_simp
    rw [beSales.eq_1, hsum, htiei]
    simp only [Finset.card_singleton, Nat.cast_one, div_one]
    rw [Function.update_self]
    have heq : a - p' - (a - c) = c - p' := by ring
    rw [heq]
    have : max (0:ℝ) (c - p') = 0 := max_eq_left (by linarith)
    rw [this]
    simp [hC.le]
  · have hnn := beSales_nonneg a C hC (Function.update (fun _ : Fin n => c) i p') i
    nlinarith


-- Case (ii): C ≤ (a-c)/(n+1), all firms priced at pstar = a - n*C.
theorem bertrand_case2 {n : ℕ} (hn : 2 ≤ n) (a c C : ℝ) (hac : c < a) (hC : 0 < C)
    (hCle : C ≤ (a - c) / (n + 1)) :
    IsBEEquilibrium a c C (fun _ : Fin n => a - n * C) := by
  set pstar := a - (n : ℝ) * C with hpstar
  intro i p'
  unfold bePayoff
  rw [Function.update_self]
  have hbase : beSales a C (fun _ : Fin n => pstar) i = C := by
    rw [beSales_of_below_empty a C _ i (by ext k; simp)]
    have htie : (Finset.univ.filter (fun k : Fin n => (fun _ : Fin n => pstar) k = pstar))
        = Finset.univ := by ext k; simp
    rw [htie, Finset.card_univ, Fintype.card_fin]
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have heq : a - pstar = (n:ℝ) * C := by rw [hpstar]; ring
    rw [heq, max_eq_right (by positivity : (0:ℝ) ≤ (n:ℝ) * C),
      mul_div_cancel_left₀ _ hnpos.ne', min_self]
  rw [hbase]
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1pos : (0:ℝ) < (n:ℝ) + 1 := by linarith
  have hcpstar : c < pstar := by
    rw [hpstar]
    have : (n:ℝ) * C ≤ (n:ℝ) * ((a - c) / ((n:ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left hCle hnpos.le
    have h2 : (n:ℝ) * ((a - c) / ((n:ℝ) + 1)) < a - c := by
      have hac' : 0 < a - c := by linarith
      calc (n:ℝ) * ((a - c) / ((n:ℝ) + 1)) = (a - c) * ((n:ℝ) / ((n:ℝ) + 1)) := by ring
        _ < (a - c) * 1 := by
            apply mul_lt_mul_of_pos_left _ hac'
            rw [div_lt_one hn1pos]; linarith
        _ = a - c := by ring
    linarith
  rcases lt_or_ge p' pstar with hp' | hp'
  · -- undercut: p' below the tied rivals, faces the full demand, still capacity-constrained.
    have hnn : beSales a C (Function.update (fun _ : Fin n => pstar) i p') i ≤ C :=
      beSales_le a C _ i
    have hpos : 0 ≤ beSales a C (Function.update (fun _ : Fin n => pstar) i p') i :=
      beSales_nonneg a C hC _ i
    rcases lt_or_ge c p' with hpc | hpc
    · have hstep : (p' - c) * beSales a C (Function.update (fun _ : Fin n => pstar) i p') i
          ≤ (p' - c) * C := mul_le_mul_of_nonneg_left hnn (by linarith)
      nlinarith
    · have hprod : (p' - c) * beSales a C (Function.update (fun _ : Fin n => pstar) i p') i
          ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos
      nlinarith
  · -- overbid: p' ≥ pstar. First, pstar - c ≥ C.
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hkey : C ≤ pstar - c := by
      rw [hpstar]
      rw [le_div_iff₀ hn1pos] at hCle
      linarith
    rcases eq_or_lt_of_le hp' with hp'e | hp'
    · -- p' = pstar: no actual deviation.
      rw [← hp'e]
      simp [hbase]
    · -- p' > pstar strictly: recompute via the recursion.
      have hn1 : 1 ≤ n - 1 := by omega
      have hrival : ∀ j : Fin n, j ≠ i →
          beSales a C (Function.update (fun _ : Fin n => pstar) i p') j = C := by
        intro j hj
        have hbelow : (Finset.univ.filter
            (fun k => Function.update (fun _ : Fin n => pstar) i p' k
              < Function.update (fun _ : Fin n => pstar) i p' j)) = ∅ := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rw [Function.update_of_ne hj]
          by_cases hk : k = i
          · subst hk; rw [Function.update_self]; linarith
          · rw [Function.update_of_ne hk]; exact lt_irrefl pstar
        have htie : (Finset.univ.filter
            (fun k => Function.update (fun _ : Fin n => pstar) i p' k
              = Function.update (fun _ : Fin n => pstar) i p' j)) = Finset.univ.erase i := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
          rw [Function.update_of_ne hj]
          by_cases hk : k = i
          · subst hk; simp only [Function.update_self, not_true_eq_false, false_and, iff_false]
            exact hp'.ne'
          · rw [Function.update_of_ne hk]; simp [hk]
        rw [beSales_of_below_empty a C _ j hbelow, htie, Function.update_of_ne hj,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
        have hn1' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          have h1n : 1 ≤ n := by omega
          rw [Nat.cast_sub h1n, Nat.cast_one]
        rw [hn1']
        have heq2 : a - pstar = (n:ℝ) * C := by rw [hpstar]; ring
        rw [heq2, max_eq_right (by positivity : (0:ℝ) ≤ (n:ℝ) * C)]
        have hge : C ≤ (n:ℝ) * C / ((n:ℝ) - 1) := by
          rw [le_div_iff₀ (by linarith [hn2] : (0:ℝ) < (n:ℝ) - 1)]
          nlinarith [hn2]
        exact min_eq_left hge
      have hsum : (∑ j ∈ (Finset.univ.filter
          (fun k => Function.update (fun _ : Fin n => pstar) i p' k
            < Function.update (fun _ : Fin n => pstar) i p' i)).attach,
          beSales a C (Function.update (fun _ : Fin n => pstar) i p') j.1) = (n - 1 : ℝ) * C := by
        have hbelowi : (Finset.univ.filter
            (fun k => Function.update (fun _ : Fin n => pstar) i p' k
              < Function.update (fun _ : Fin n => pstar) i p' i)) = Finset.univ.erase i := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
          rw [Function.update_self]
          by_cases hk : k = i
          · subst hk; simp
          · rw [Function.update_of_ne hk]; simp [hk, hp']
        rw [hbelowi]
        have hconst : ∀ j ∈ (Finset.univ.erase i).attach,
            beSales a C (Function.update (fun _ : Fin n => pstar) i p') j.1 = C := by
          intro j _
          exact hrival j.1 (Finset.ne_of_mem_erase j.2)
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_attach,
          Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have h1n : 1 ≤ n := by omega
        rw [Nat.cast_sub h1n, Nat.cast_one]
      have htiei : (Finset.univ.filter
          (fun k => Function.update (fun _ : Fin n => pstar) i p' k
            = Function.update (fun _ : Fin n => pstar) i p' i)) = {i} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [Function.update_self]
        by_cases hk : k = i
        · subst hk; simp
        · rw [Function.update_of_ne hk]; simp only [hk, iff_false]; exact hp'.ne
      rw [beSales.eq_1, hsum, htiei]
      simp only [Finset.card_singleton, Nat.cast_one, div_one]
      rw [Function.update_self]
      have heq3 : a - p' - ((n:ℝ) - 1) * C = pstar + C - p' := by rw [hpstar]; ring
      rw [heq3]
      rcases lt_or_ge p' (pstar + C) with hcap | hcap
      · have h0 : max (0:ℝ) (pstar + C - p') = pstar + C - p' := max_eq_right (by linarith)
        rw [h0]
        have hle : pstar + C - p' ≤ C := by linarith
        rw [min_eq_right hle]
        nlinarith [hkey, sq_nonneg (p' - pstar)]
      · have h0 : max (0:ℝ) (pstar + C - p') = 0 := max_eq_left (by linarith)
        rw [h0]
        have : min C (0:ℝ) = 0 := min_eq_right hC.le
        rw [this]
        nlinarith [hcpstar, hC]

end RevenueManagement

open RevenueManagement
theorem solution {n : ℕ} (hn : 2 ≤ n) (a c C : ℝ) (hac : c < a) (hC : 0 < C) :
    ((a - c) / (n - 1) ≤ C →
      IsBEEquilibrium a c C (fun _ : Fin n => c) ∧ ∀ i, bePayoff a c C (fun _ : Fin n => c) i = 0) ∧
    (C ≤ (a - c) / (n + 1) → IsBEEquilibrium a c C (fun _ : Fin n => a - n * C)) :=
  ⟨fun h => bertrand_case1 hn a c C hac hC h, fun h => bertrand_case2 hn a c C hac hC h⟩

