-- Prove2me | solution 1 for OpenSearchElectionTimer.contested_prob_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T01:27:09.403234+00:00
-- url     : https://prove2.me/submissions/a56ab42a-2984-4a76-bef5-c4f61acd9464

import Definitions.Def_OpenSearchElectionTimer
import Theorems.Thm_OpenSearchElectionTimer_randomDelay_near_uniform
import Theorems.Thm_OpenSearchElectionTimer_randomDelay_range

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

/-- The ceiling `⌈N / b⌉ = (N + b - 1) / b` is antitone in `b ≥ 1`. -/
private theorem ceil_div_anti (N a b : ℕ) (hN : 1 ≤ N) (ha : 1 ≤ a) (hab : a ≤ b) :
    (N + b - 1) / b ≤ (N + a - 1) / a := by
  have h1 : N + b - 1 = (N - 1) + b := by omega
  have h2 : N + a - 1 = (N - 1) + a := by omega
  rw [h1, h2, Nat.add_div_right _ (by omega), Nat.add_div_right _ (by omega)]
  exact Nat.add_le_add_right (Nat.div_le_div_left hab (by omega)) 1

/-- For a fixed target `t`, few draws give a delay within `δ` of `t`. -/
private theorem card_close_le (t : ℤ) (Mb Mmin δ : ℕ) (hM : 1 ≤ Mmin)
    (hMb : Mmin ≤ Mb ∧ Mb ≤ 2 ^ 63) (hδ : 1 ≤ δ) :
    (Finset.univ.filter (fun y : Fin (2 ^ 64) => |t - (randomDelay Mb y : ℤ)| < δ)).card ≤
      (2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin)) := by
  have key := Finset.card_le_mul_card_image_of_maps_to
    (f := fun y : Fin (2 ^ 64) => (randomDelay Mb y : ℤ))
    (s := Finset.univ.filter (fun y : Fin (2 ^ 64) => |t - (randomDelay Mb y : ℤ)| < δ))
    (t := Finset.Ioo (t - δ) (t + δ)) ?_ (2 * ((2 ^ 63 + Mmin - 1) / Mmin)) ?_
  · rw [Int.card_Ioo] at key
    have e : (t + δ - (t - δ) - 1).toNat = 2 * δ - 1 := by omega
    rw [e] at key
    rw [Nat.mul_comm]; exact key
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_Ioo]
    rw [abs_lt] at hy
    constructor <;> linarith [hy.1, hy.2]
  · intro e _
    calc (Finset.filter (fun y => (randomDelay Mb y : ℤ) = e)
          (Finset.univ.filter (fun y : Fin (2 ^ 64) => |t - (randomDelay Mb y : ℤ)| < δ))).card
        ≤ (Finset.univ.filter (fun y : Fin (2 ^ 64) => (randomDelay Mb y : ℤ) = e)).card := by
          apply Finset.card_le_card
          intro y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun h => h.2
      _ ≤ 2 * ((2 ^ 63 + Mmin - 1) / Mmin) := by
          by_cases he : 1 ≤ e ∧ e ≤ Mb
          · obtain ⟨d, rfl⟩ : ∃ d : ℕ, e = d := ⟨e.toNat, by omega⟩
            simp only [Nat.cast_inj]
            have h1 := (OpenSearchElectionTimer.randomDelay_near_uniform Mb d (by omega) hMb.2
              (by omega) (by omega)).2
            exact h1.trans (Nat.mul_le_mul_left _ (ceil_div_anti _ _ _ (by norm_num) hM hMb.1))
          · have : Finset.univ.filter (fun y : Fin (2 ^ 64) => (randomDelay Mb y : ℤ) = e) = ∅ := by
              ext y
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                iff_false]
              intro h
              have := OpenSearchElectionTimer.randomDelay_range Mb (by omega) y
              omega
            rw [this, Finset.card_empty]
            exact Nat.zero_le _

/-- Sum over `ι → A` by splitting off the coordinate `j`. -/
private theorem sum_piSplitAt {ι A M : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    [AddCommMonoid M] (j : ι) (F : (ι → A) → M) :
    ∑ x, F x = ∑ r : {k // k ≠ j} → A, ∑ y : A, F ((Equiv.piSplitAt j (fun _ => A)).symm (y, r)) := by
  rw [← (Equiv.piSplitAt j (fun _ => A)).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]

/-- The coordinate split off by `Equiv.piSplitAt`. -/
private theorem piSplitAt_symm_self {ι A : Type*} [DecidableEq ι] (j : ι) (y : A)
    (r : {k // k ≠ j} → A) : (Equiv.piSplitAt j (fun _ => A)).symm (y, r) j = y := by
  simp [Equiv.piSplitAt_symm_apply]

/-- The other coordinates. -/
private theorem piSplitAt_symm_ne {ι A : Type*} [DecidableEq ι] (j : ι) (y : A)
    (r : {k // k ≠ j} → A) (k : ι) (hk : k ≠ j) :
    (Equiv.piSplitAt j (fun _ => A)).symm (y, r) k = r ⟨k, hk⟩ := by
  simp [Equiv.piSplitAt_symm_apply, hk]

/-- There are `C(n, 2)` pairs `i < j` in `Fin n`. -/
private theorem card_pairs_lt (n : ℕ) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 < ij.2)).card = n.choose 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h : ∀ j : Fin n, (∑ i : Fin n, if (i, j).1 < (i, j).2 then 1 else 0) = j.val := by
    intro j
    rw [← Finset.card_filter, ← Fin.card_Iio j]
    congr 1
    ext i
    simp
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun m => m) n, Nat.choose_two_right, ← Finset.sum_range_id_mul_two,
    Nat.mul_div_cancel _ (by norm_num)]

/-- For two distinct candidates, few full draws make them fire less than `δ` apart. -/
private theorem card_pair_close_le (n δ Mmin : ℕ) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin n → Int) (bound : Fin n → Nat) (hbound : ∀ i, Mmin ≤ bound i ∧ bound i ≤ 2 ^ 63)
    (i j : Fin n) (hij : i ≠ j) :
    (Finset.univ.filter (fun x : Fin n → Fin (2 ^ 64) =>
        |fireTime offset bound x i - fireTime offset bound x j| < δ)).card ≤
      (2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin))) := by
  rw [Finset.card_filter, sum_piSplitAt j]
  calc ∑ r : {k // k ≠ j} → Fin (2 ^ 64), ∑ y : Fin (2 ^ 64),
        (if |fireTime offset bound ((Equiv.piSplitAt j (fun _ => Fin (2 ^ 64))).symm (y, r)) i -
            fireTime offset bound ((Equiv.piSplitAt j (fun _ => Fin (2 ^ 64))).symm (y, r)) j| < δ
          then 1 else 0)
      = ∑ r : {k // k ≠ j} → Fin (2 ^ 64), (Finset.univ.filter (fun y : Fin (2 ^ 64) =>
          |(offset i + randomDelay (bound i) (r ⟨i, hij⟩) - offset j) -
            (randomDelay (bound j) y : ℤ)| < δ)).card := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro y _
        unfold fireTime
        rw [piSplitAt_symm_self, piSplitAt_symm_ne _ _ _ _ hij]
        have : offset i + (randomDelay (bound i) (r ⟨i, hij⟩) : ℤ) -
            (offset j + (randomDelay (bound j) y : ℤ)) =
            (offset i + randomDelay (bound i) (r ⟨i, hij⟩) - offset j) -
              (randomDelay (bound j) y : ℤ) := by ring
        rw [this]
    _ ≤ ∑ _r : {k // k ≠ j} → Fin (2 ^ 64),
          (2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin)) :=
        Finset.sum_le_sum (fun r _ => card_close_le _ (bound j) Mmin δ hM (hbound j) hδ)
    _ = (2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin))) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        congr 1
        simp

/-- **A round of competing timers is contested with probability at most `contestedBound n δ Mmin`.** For `n ≥ 1`
candidates with arbitrary offsets and with bounds between `Mmin ≥ 1` and `2^63`, the probability that no candidate fires
at least `δ ≥ 1` before all others is at most `contestedBound n δ Mmin = C(n,2) · (2δ - 1) · ⌈2^63 / Mmin⌉ / 2^63`,
which is small only when `Mmin` is much larger than `C(n,2) · (2δ - 1)`. -/
theorem solution (n δ Mmin : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hM : 1 ≤ Mmin)
    (offset : Fin n → Int) (bound : Fin n → Nat) (hbound : ∀ i, Mmin ≤ bound i ∧ bound i ≤ 2 ^ 63) :
    ((Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x)).card : ℚ) / (2 ^ 64) ^ n ≤
      contestedBound n δ Mmin := by
  set P := (Finset.univ : Finset (Fin n × Fin n)).filter (fun ij => ij.1 < ij.2) with hPdef
  set E : Fin n × Fin n → Finset (Fin n → Fin (2 ^ 64)) := fun ij =>
    Finset.univ.filter (fun x => |fireTime offset bound x ij.1 - fireTime offset bound x ij.2| < δ)
    with hEdef
  have hsub : Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x) ⊆ P.biUnion E := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fireTime offset bound x)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    unfold Uncontested at hx
    push Not at hx
    obtain ⟨j, hj, hlt⟩ := hx i0
    have hle := hi0 j (Finset.mem_univ _)
    simp only [Finset.mem_biUnion, hPdef, hEdef, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_or_gt_of_ne hj with h | h
    · exact ⟨(j, i0), h, by rw [abs_lt]; constructor <;> linarith⟩
    · exact ⟨(i0, j), h, by rw [abs_lt]; constructor <;> linarith⟩
  have hcount : (Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x)).card ≤
      n.choose 2 * ((2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin)))) := by
    calc _ ≤ (P.biUnion E).card := Finset.card_le_card hsub
      _ ≤ ∑ ij ∈ P, (E ij).card := Finset.card_biUnion_le
      _ ≤ ∑ _ij ∈ P, (2 ^ 64) ^ (n - 1) * ((2 * δ - 1) * (2 * ((2 ^ 63 + Mmin - 1) / Mmin))) := by
          apply Finset.sum_le_sum
          intro ij hij
          simp only [hPdef, Finset.mem_filter, Finset.mem_univ, true_and] at hij
          exact card_pair_close_le n δ Mmin hδ hM offset bound hbound ij.1 ij.2 (ne_of_lt hij)
      _ = _ := by rw [Finset.sum_const, hPdef, card_pairs_lt, smul_eq_mul]
  have hq : ((Finset.univ.filter (fun x => ¬ Uncontested offset bound δ x)).card : ℚ) ≤
      (n.choose 2 : ℚ) * (((2 : ℚ) ^ 64) ^ (n - 1) * (((2 * δ - 1 : ℕ) : ℚ) *
        (2 * (((2 ^ 63 + Mmin - 1) / Mmin : ℕ) : ℚ)))) := by
    exact_mod_cast hcount
  have hpow : ((2 : ℚ) ^ 64) ^ n = ((2 : ℚ) ^ 64) ^ (n - 1) * 2 ^ 64 := by
    rw [← pow_succ]; congr 1; omega
  unfold contestedBound
  rw [div_le_div_iff₀ (by positivity) (by positivity), hpow]
  calc _ ≤ (n.choose 2 : ℚ) * (((2 : ℚ) ^ 64) ^ (n - 1) * (((2 * δ - 1 : ℕ) : ℚ) *
        (2 * (((2 ^ 63 + Mmin - 1) / Mmin : ℕ) : ℚ)))) * 2 ^ 63 :=
        mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by ring
