-- Prove2me | solution 1 for TaoFivePrimes.typeII_counting_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T04:59:49.190533+00:00
-- url     : https://prove2.me/submissions/2203256c-553c-4f58-9856-cd0940aae660

import Mathlib

open Finset

section PartS5C
open Finset
namespace TaoS5C

/-- A set of odd integers inside a real interval has at most `(v-u)/2 + 1` elements. -/
theorem card_odd_le (u v : ℝ) (huv : u ≤ v) (S : Finset ℤ)
    (hodd : ∀ n ∈ S, Odd n) (hmem : ∀ n ∈ S, u ≤ (n : ℝ) ∧ (n : ℝ) ≤ v) :
    (S.card : ℝ) ≤ (v - u) / 2 + 1 := by
  classical
  · set A : ℤ := ⌈(u - 1) / 2⌉ with hA
    set B : ℤ := ⌊(v - 1) / 2⌋ with hB
    have hinj : Set.InjOn (fun n : ℤ => (n - 1) / 2) S := by
      intro m hm n hn h
      obtain ⟨j, hj⟩ := hodd m hm
      obtain ⟨k, hk⟩ := hodd n hn
      simp only [hj, hk] at h ⊢
      omega
    have hsub : S.image (fun n : ℤ => (n - 1) / 2) ⊆ Finset.Icc A B := by
      intro z hz
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨j, hj⟩ := hodd n hn
      obtain ⟨hlo, hhi⟩ := hmem n hn
      have hval : (n - 1) / 2 = j := by omega
      rw [hval]
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · rw [hA, Int.ceil_le]
        have : ((n : ℤ) : ℝ) = 2 * (j : ℝ) + 1 := by
          have : (n : ℤ) = 2 * j + 1 := by omega
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)] at *
        linarith [hlo, this]
      · rw [hB, Int.le_floor]
        have : ((n : ℤ) : ℝ) = 2 * (j : ℝ) + 1 := by
          have : (n : ℤ) = 2 * j + 1 := by omega
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        linarith [hhi, this]
    have hcard : S.card = (S.image (fun n : ℤ => (n - 1) / 2)).card :=
      (Finset.card_image_of_injOn hinj).symm
    have hcard2 : (S.image (fun n : ℤ => (n - 1) / 2)).card ≤ (Finset.Icc A B).card :=
      Finset.card_le_card hsub
    have hBA : (B : ℝ) - (A : ℝ) ≤ (v - u) / 2 := by
      have h1 : (B : ℝ) ≤ (v - 1) / 2 := Int.floor_le _
      have h2 : (u - 1) / 2 ≤ (A : ℝ) := Int.le_ceil _
      linarith
    have hfin : ((Finset.Icc A B).card : ℝ) ≤ (v - u) / 2 + 1 := by
      rw [Int.card_Icc]
      by_cases h : B + 1 - A ≤ 0
      · have hz : ((B + 1 - A).toNat : ℤ) = 0 := by omega
        have h0 : (((B + 1 - A).toNat : ℕ) : ℝ) = 0 := by exact_mod_cast hz
        rw [h0]
        linarith
      · have hz : (((B + 1 - A).toNat : ℕ) : ℤ) = B + 1 - A := by omega
        have hr : (((B + 1 - A).toNat : ℕ) : ℝ) = ((B : ℝ) + 1 - (A : ℝ)) := by
          have hc := congrArg (fun z : ℤ => (z : ℝ)) hz
          push_cast at hc
          exact hc
        rw [hr]
        linarith [hBA]
    calc (S.card : ℝ) = ((S.image (fun n : ℤ => (n - 1) / 2)).card : ℝ) := by rw [hcard]
      _ ≤ ((Finset.Icc A B).card : ℝ) := by exact_mod_cast hcard2
      _ ≤ (v - u) / 2 + 1 := hfin

/-- **Tao, Section 5**: the two counting bounds in the estimation of the Type II sum. -/
theorem typeII_counting (x W : ℝ) (hx : 0 < x) (hW : 2 ≤ W)
    (S T : Finset ℤ)
    (hS : ∀ n ∈ S, Odd n) (hSm : ∀ n ∈ S, x / (2 * W) ≤ (n : ℝ) ∧ (n : ℝ) ≤ x / W)
    (hT : ∀ n ∈ T, Odd n) (hTm : ∀ n ∈ T, W / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ W) :
    (S.card : ℝ) ≤ x / (4 * W) + 1
      ∧ (∑ n ∈ T, Real.log (n : ℝ) ^ 2) ≤ (W / 4 + 1) * Real.log W ^ 2 := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg (by linarith)
  constructor
  · have huv : x / (2 * W) ≤ x / W := by
      rw [div_le_div_iff₀ (by positivity) hW0]
      nlinarith
    have h := card_odd_le (x / (2 * W)) (x / W) huv S hS hSm
    have heq : (x / W - x / (2 * W)) / 2 + 1 = x / (4 * W) + 1 := by
      field_simp
      ring
    linarith [h, heq]
  · have hbnd : ∀ n ∈ T, Real.log (n : ℝ) ^ 2 ≤ Real.log W ^ 2 := by
      intro n hn
      obtain ⟨h1, h2⟩ := hTm n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
      have hl0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
      have hl1 : Real.log (n : ℝ) ≤ Real.log W := Real.log_le_log (by linarith) h2
      nlinarith
    have hsum : (∑ n ∈ T, Real.log (n : ℝ) ^ 2) ≤ (T.card : ℝ) * Real.log W ^ 2 := by
      calc (∑ n ∈ T, Real.log (n : ℝ) ^ 2) ≤ ∑ _n ∈ T, Real.log W ^ 2 :=
            Finset.sum_le_sum hbnd
        _ = (T.card : ℝ) * Real.log W ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard := card_odd_le (W / 2) W (by linarith) T hT hTm
    have heq : (W - W / 2) / 2 + 1 = W / 4 + 1 := by ring
    rw [heq] at hcard
    have hsq : (0 : ℝ) ≤ Real.log W ^ 2 := sq_nonneg _
    nlinarith [hsum, hcard, hsq]

end TaoS5C
end PartS5C

theorem solution (x W : ℝ) (hx : 0 < x) (hW : 2 ≤ W)
    (S T : Finset ℤ)
    (hS : ∀ n ∈ S, Odd n) (hSm : ∀ n ∈ S, x / (2 * W) ≤ (n : ℝ) ∧ (n : ℝ) ≤ x / W)
    (hT : ∀ n ∈ T, Odd n) (hTm : ∀ n ∈ T, W / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ W) :
    (S.card : ℝ) ≤ x / (4 * W) + 1
      ∧ (∑ n ∈ T, Real.log (n : ℝ) ^ 2) ≤ (W / 4 + 1) * Real.log W ^ 2 :=
  TaoS5C.typeII_counting x W hx hW S T hS hSm hT hTm
