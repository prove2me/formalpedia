-- Prove2me | solution 1 for ParallelLotteries.two_item_welfare_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:38:41.144083+00:00
-- url     : https://prove2.me/submissions/b5a5073c-9025-4832-9e5f-8d7d9af87591

import Mathlib
import Definitions.Def_ParallelLotteries_Model

namespace Aux_PLtwo
open ParallelLotteries

theorem sum_single {n k : ℕ} (i : Fin n) :
    ∑ l, ((if l = i then Fin.last k else 0 : Fin (k + 1)) : ℕ) ≤ k := by
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp

def single {n k : ℕ} (i : Fin n) : Strategy n k :=
  (⟨(fun l => if l = i then Fin.last k else 0, 1), sum_single i⟩ :
    {s : (Fin n → Fin (k + 1)) × Equiv.Perm (Fin n) // ∑ i, (s.1 i : ℕ) ≤ k})

theorem tickets_single {n k : ℕ} (i l : Fin n) :
    (single (k := k) i).tickets l = if l = i then k else 0 := by
  unfold Strategy.tickets single
  by_cases h : l = i <;> simp [h]

theorem rank_single {n k : ℕ} (i : Fin n) : (single (k := k) i).rank = 1 := rfl

theorem welfare_single {n k : ℕ} (v p : Fin n → ℝ) (i : Fin n) :
    welfare v (single (k := k) i) p = v i * (1 - (1 - p i) ^ k) := by
  unfold welfare
  rw [Finset.sum_eq_single i]
  · unfold chi
    rw [tickets_single, if_pos rfl, Finset.prod_eq_one, mul_one]
    intro j hj
    rw [rank_single] at hj
    have hj' : j < i := by
      have := (Finset.mem_filter.mp hj).2
      simpa using this
    rw [tickets_single, if_neg (ne_of_lt hj'), pow_zero]
  · intro b _ hb
    unfold chi
    rw [tickets_single, if_neg hb, pow_zero, sub_self, zero_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

end Aux_PLtwo

open ParallelLotteries in
theorem solution {n k : ℕ} (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ l, 0 ≤ p l ∧ p l ≤ 1) (Φ : (Fin n → ℝ) → Strategy n k) (hΦ : IsOptimal p Φ)
    (v : Fin n → ℝ) (i j : Fin n) :
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      α * (1 - (1 - p i) ^ k) * v i + (1 - α) * (1 - (1 - p j) ^ k) * v j ≤
        welfare v (Φ v) p) ∧
    (∀ yi yj : ℝ, 0 < p i → 0 < p j → 0 ≤ yi → 0 ≤ yj → 0 < yi + yj →
      yi * v i + yj * v j ≤
        (yi / (1 - (1 - p i) ^ k) + yj / (1 - (1 - p j) ^ k)) * welfare v (Φ v) p) := by
  have hWi := hΦ v (Aux_PLtwo.single i)
  have hWj := hΦ v (Aux_PLtwo.single j)
  rw [Aux_PLtwo.welfare_single] at hWi hWj
  set W := welfare v (Φ v) p
  refine ⟨fun α h0 h1 => ?_, fun yi yj hpi hpj hyi hyj _ => ?_⟩
  · have e1 := mul_le_mul_of_nonneg_left hWi h0
    have e2 := mul_le_mul_of_nonneg_left hWj (by linarith : (0 : ℝ) ≤ 1 - α)
    nlinarith
  · have hq : ∀ l, 0 < p l → 0 < 1 - (1 - p l) ^ k := by
      intro l hl
      have : (1 - p l) ^ k < 1 :=
        pow_lt_one₀ (by linarith [(hp l).2]) (by linarith) (by omega)
      linarith
    have qi := hq i hpi
    have qj := hq j hpj
    have f1 : yi * v i = yi / (1 - (1 - p i) ^ k) * (v i * (1 - (1 - p i) ^ k)) := by
      field_simp
    have f2 : yj * v j = yj / (1 - (1 - p j) ^ k) * (v j * (1 - (1 - p j) ^ k)) := by
      field_simp
    have g1 := mul_le_mul_of_nonneg_left hWi (div_nonneg hyi qi.le)
    have g2 := mul_le_mul_of_nonneg_left hWj (div_nonneg hyj qj.le)
    rw [f1, f2, add_mul]
    linarith
