-- Prove2me | solution 1 for OpenSearchElectionTimer.randomDelay_card
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T01:23:35.072802+00:00
-- url     : https://prove2.me/submissions/a644ae0a-201f-4841-b062-2564cbfeb538

import Definitions.Def_OpenSearchElectionTimer

open OpenSearchPreVote OpenSearchElectionTimer

/-- `nonNegative (toLong x)` in terms of `x.val`: the lower half of `Fin (2^64)` (the negative longs and
`Long.MIN_VALUE`) goes to `(2^63 - x) % 2^63`, the upper half (the non-negative longs) to `x - 2^63`. -/
private theorem nonNegative_toLong (x : Fin (2 ^ 64)) :
    nonNegative (toLong x) = if x.val < 2 ^ 63 then (2 ^ 63 - x.val) % 2 ^ 63 else x.val - 2 ^ 63 := by
  have hx := x.isLt
  unfold nonNegative toLong
  split_ifs <;> omega

/-- `nonNegative ∘ toLong` is exactly two-to-one from `Fin (2^64)` onto `[0, 2^63)`. -/
private theorem card_filter_nonNegative (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => P (nonNegative (toLong x)))).card =
      2 * ((Finset.range (2 ^ 63)).filter P).card := by
  rw [← Finset.card_filter_add_card_filter_not (p := fun x : Fin (2 ^ 64) => x.val < 2 ^ 63),
    Finset.filter_filter, Finset.filter_filter]
  have h1 : (Finset.univ.filter (fun x : Fin (2 ^ 64) =>
      P (nonNegative (toLong x)) ∧ x.val < 2 ^ 63)).card = ((Finset.range (2 ^ 63)).filter P).card := by
    apply Finset.card_nbij' (fun x => (2 ^ 63 - x.val) % 2 ^ 63)
      (fun w => ⟨(2 ^ 63 - w) % 2 ^ 63, by omega⟩)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_range] at hx ⊢
      rw [nonNegative_toLong, if_pos hx.2] at hx
      exact ⟨by omega, hx.1⟩
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_range] at hw ⊢
      have hlt : (2 ^ 63 - w) % 2 ^ 63 < 2 ^ 63 := Nat.mod_lt _ (by norm_num)
      refine ⟨?_, hlt⟩
      rw [nonNegative_toLong, if_pos hlt]
      have : (2 ^ 63 - (2 ^ 63 - w) % 2 ^ 63) % 2 ^ 63 = w := by omega
      rw [this]; exact hw.2
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
      ext; simp only; omega
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hw
      simp only; omega
  have h2 : (Finset.univ.filter (fun x : Fin (2 ^ 64) =>
      P (nonNegative (toLong x)) ∧ ¬ x.val < 2 ^ 63)).card = ((Finset.range (2 ^ 63)).filter P).card := by
    apply Finset.card_nbij' (fun x => x.val - 2 ^ 63)
      (fun w => ⟨(w % 2 ^ 63) + 2 ^ 63, by omega⟩)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_range] at hx ⊢
      rw [nonNegative_toLong, if_neg hx.2] at hx
      exact ⟨by omega, hx.1⟩
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Finset.mem_range] at hw ⊢
      have hlt : ¬ (w % 2 ^ 63) + 2 ^ 63 < 2 ^ 63 := by omega
      refine ⟨?_, hlt⟩
      rw [nonNegative_toLong, if_neg hlt]
      have : (w % 2 ^ 63) + 2 ^ 63 - 2 ^ 63 = w := by omega
      rw [this]; exact hw.2
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
      ext; simp only; omega
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hw
      simp only; omega
  rw [h1, h2]; ring

/-- The `w < N` with `w % M = d - 1` are the `d - 1 + k M` for `k ≤ (N - d) / M`. -/
private theorem card_mod_eq (N M d : ℕ) (hM : 1 ≤ M) (hd : 1 ≤ d) (hdM : d ≤ M) (hMN : M ≤ N) :
    ((Finset.range N).filter (fun w => w % M + 1 = d)).card = (N - d) / M + 1 := by
  have key : (Finset.range N).filter (fun w => w % M + 1 = d) =
      (Finset.range ((N - d) / M + 1)).image (fun k => d - 1 + k * M) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hw, hwd⟩
      have h := Nat.div_add_mod w M
      have hc : M * (w / M) = w / M * M := Nat.mul_comm _ _
      refine ⟨w / M, ?_, ?_⟩
      · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le (by omega)]
        omega
      · omega
    · rintro ⟨k, hk, rfl⟩
      have hk' : k * M ≤ N - d := by
        have : k ≤ (N - d) / M := by omega
        calc k * M ≤ (N - d) / M * M := Nat.mul_le_mul_right _ this
          _ ≤ N - d := Nat.div_mul_le_self _ _
      constructor
      · omega
      · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]; omega
  rw [key, Finset.card_image_of_injective, Finset.card_range]
  intro k1 k2 h
  simp only at h
  have : k1 * M = k2 * M := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

/-- **The exact distribution of a delay.** For a bound `1 ≤ M ≤ 2^63` and `1 ≤ d ≤ M`, exactly
`2 · (⌊(2^63 - d) / M⌋ + 1)` of the `2^64` values of `random.nextLong()` give the delay `d`. -/
theorem solution (M d : Nat) (hM : 1 ≤ M) (hM' : M ≤ 2 ^ 63)
    (hd : 1 ≤ d) (hdM : d ≤ M) :
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card = 2 * ((2 ^ 63 - d) / M + 1) := by
  unfold randomDelay toPositiveLongAtMost
  rw [card_filter_nonNegative (fun w => w % M + 1 = d), card_mod_eq _ _ _ hM hd hdM hM']
