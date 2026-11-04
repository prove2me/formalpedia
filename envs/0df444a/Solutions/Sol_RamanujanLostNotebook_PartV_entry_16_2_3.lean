-- Prove2me | solution 1 for RamanujanLostNotebook.PartV.entry_16_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-03T22:14:02.088206+00:00
-- url     : https://prove2.me/submissions/6ba93270-427d-47ee-a1e8-9fab7044c00d

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch16_rrcfDen
import Definitions.Def_RamanujanLostNotebook_PartV_ch16_rrcfNum

namespace RRCFAux
open RamanujanLostNotebook.PartV

/-- Gaussian binomial coefficient `[n, i]_x`, defined by the Pascal recursion. -/
noncomputable def gb (x : ℂ) : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, i + 1 => gb x n i + x ^ (i + 1) * gb x n (i + 1)

lemma gb_zero_right (x : ℂ) (n : ℕ) : gb x n 0 = 1 := by
  cases n <;> simp [gb]

lemma gb_gt (x : ℂ) : ∀ n i : ℕ, n < i → gb x n i = 0
  | 0, i, h => by
      cases i with
      | zero => omega
      | succ i => simp [gb]
  | n + 1, i, h => by
      cases i with
      | zero => omega
      | succ i => simp [gb, gb_gt x n i (by omega), gb_gt x n (i + 1) (by omega)]

lemma gb_self (x : ℂ) : ∀ n : ℕ, gb x n n = 1
  | 0 => by simp [gb]
  | n + 1 => by simp [gb, gb_self x n, gb_gt x n (n + 1) (by omega)]

lemma gb_pascal2 (x : ℂ) : ∀ n i : ℕ,
    gb x (n + 1) (i + 1) = x ^ (n - i) * gb x n i + gb x n (i + 1) := by
  intro n
  induction n with
  | zero =>
    intro i
    cases i with
    | zero => simp [gb]
    | succ i => simp [gb]
  | succ n ih =>
    intro i
    by_cases hi : i ≤ n
    · -- ratio identity `(1 - x^(n+1-i)) [n+1, i] = (1 - x^(n+1)) [n, i]`
      have R : (1 - x ^ (n + 1 - i)) * gb x (n + 1) i = (1 - x ^ (n + 1)) * gb x n i := by
        cases i with
        | zero => simp [gb_zero_right]
        | succ i' =>
          have hih := ih i'
          have hdef : gb x (n + 1) (i' + 1)
              = gb x n i' + x ^ (i' + 1) * gb x n (i' + 1) := rfl
          have hyu : x ^ (n - i') * x ^ (i' + 1) = x ^ (n + 1) := by
            rw [← pow_add]; congr 1; omega
          have hn : n + 1 - (i' + 1) = n - i' := by omega
          rw [hn]
          linear_combination hih - x ^ (n - i') * hdef - gb x n (i' + 1) * hyu
      have hdef : gb x (n + 2) (i + 1)
          = gb x (n + 1) i + x ^ (i + 1) * gb x (n + 1) (i + 1) := rfl
      have hdef2 : gb x (n + 1) (i + 1)
          = gb x n i + x ^ (i + 1) * gb x n (i + 1) := rfl
      have hih := ih i
      have hyu : x ^ (n - i) * x ^ (i + 1) = x ^ (n + 1) := by
        rw [← pow_add]; congr 1; omega
      have hn : n + 1 - i = n + 1 - i := rfl
      rw [hdef]
      linear_combination R - hdef2 + x ^ (i + 1) * hih + gb x n i * hyu
    · have hi' : n < i := by omega
      by_cases hi2 : i = n + 1
      · subst hi2
        have z : gb x (n + 1) (n + 1 + 1) = 0 := gb_gt x _ _ (by omega)
        simp [gb_self, z]
      · have h1 : gb x (n + 1) i = 0 := gb_gt x _ _ (by omega)
        have h2 : gb x (n + 1) (i + 1) = 0 := gb_gt x _ _ (by omega)
        have h3 : gb x (n + 2) (i + 1) = 0 := gb_gt x _ _ (by omega)
        rw [h1, h2, h3]; simp


/-- Ratio identity `(1 - x^(i+1)) [n+1, i+1] = (1 - x^(n+1)) [n, i]`. -/
lemma gb_ratio (x : ℂ) (n i : ℕ) :
    (1 - x ^ (i + 1)) * gb x (n + 1) (i + 1) = (1 - x ^ (n + 1)) * gb x n i := by
  have hdef : gb x (n + 1) (i + 1) = gb x n i + x ^ (i + 1) * gb x n (i + 1) := rfl
  have hp := gb_pascal2 x n i
  by_cases hi : i ≤ n
  · have hyu : x ^ (n - i) * x ^ (i + 1) = x ^ (n + 1) := by
      rw [← pow_add]; congr 1; omega
    linear_combination hdef - x ^ (i + 1) * hp - gb x n i * hyu
  · have h1 : gb x n i = 0 := gb_gt x _ _ (by omega)
    have h2 : gb x (n + 1) (i + 1) = 0 := gb_gt x _ _ (by omega)
    rw [h1, h2]; simp

/-- At a primitive `(m+1)`-th root of unity the interior q-binomials `[m+1, i+1]`, `i < m`, vanish. -/
lemma gb_root (x : ℂ) (m : ℕ) (hx : IsPrimitiveRoot x (m + 1)) (i : ℕ) (hi : i < m) :
    gb x (m + 1) (i + 1) = 0 := by
  have h := gb_ratio x m i
  have h1 : x ^ (m + 1) = 1 := hx.pow_eq_one
  have h2 : x ^ (i + 1) ≠ 1 := hx.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  rw [h1, sub_self, zero_mul] at h
  have : (1 - x ^ (i + 1)) ≠ 0 := sub_ne_zero.mpr (Ne.symm h2)
  exact (mul_eq_zero.mp h).resolve_left this

/-- Gaussian binomial with integer lower index (zero outside `0 ≤ k ≤ n`). -/
noncomputable def gz (x : ℂ) (n : ℕ) (k : ℤ) : ℂ := if 0 ≤ k then gb x n k.toNat else 0

lemma gz_neg (x : ℂ) (n : ℕ) {k : ℤ} (h : k < 0) : gz x n k = 0 := by
  simp [gz, not_le.mpr h]

lemma gz_nat (x : ℂ) (n i : ℕ) : gz x n (i : ℤ) = gb x n i := by
  simp [gz]

lemma gz_gt (x : ℂ) (n : ℕ) {k : ℤ} (h : (n : ℤ) < k) : gz x n k = 0 := by
  have hk : 0 ≤ k := by omega
  obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rw [gz_nat]; exact gb_gt x _ _ (by omega)

lemma gz_pascal1 (x : ℂ) (hx : x ≠ 0) (n : ℕ) (k : ℤ) :
    gz x (n + 1) k = gz x n (k - 1) + x ^ k * gz x n k := by
  rcases lt_or_ge k 0 with h | h
  · rw [gz_neg x _ h, gz_neg x _ h, gz_neg x _ (by omega)]; simp
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le h
    cases i with
    | zero =>
      rw [gz_neg x _ (show ((0 : ℕ) : ℤ) - 1 < 0 by omega)]
      simp [gz, gb_zero_right]
    | succ i =>
      have e : (((i + 1 : ℕ) : ℤ) - 1) = (i : ℤ) := by push_cast; ring
      rw [e, gz_nat, gz_nat, gz_nat, zpow_natCast]
      rfl

lemma gz_pascal2 (x : ℂ) (hx : x ≠ 0) (n : ℕ) (k : ℤ) :
    gz x (n + 1) k = x ^ ((n : ℤ) + 1 - k) * gz x n (k - 1) + gz x n k := by
  rcases lt_or_ge k 0 with h | h
  · rw [gz_neg x _ h, gz_neg x _ h, gz_neg x _ (by omega)]; simp
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le h
    cases i with
    | zero =>
      rw [gz_neg x _ (show ((0 : ℕ) : ℤ) - 1 < 0 by omega)]
      simp [gz, gb_zero_right]
    | succ i =>
      have e : (((i + 1 : ℕ) : ℤ) - 1) = (i : ℤ) := by push_cast; ring
      rw [e, gz_nat, gz_nat, gz_nat]
      by_cases hi : i ≤ n
      · have e2 : (n : ℤ) + 1 - ((i + 1 : ℕ) : ℤ) = ((n - i : ℕ) : ℤ) := by
          push_cast [Nat.cast_sub hi]; ring
        rw [e2, zpow_natCast]
        exact gb_pascal2 x n i
      · have h1 : gb x n i = 0 := gb_gt x _ _ (by omega)
        have h2 : gb x n (i + 1) = 0 := gb_gt x _ _ (by omega)
        have h3 : gb x (n + 1) (i + 1) = 0 := gb_gt x _ _ (by omega)
        rw [h1, h2, h3]; simp

lemma gz_L1 (x : ℂ) (hx : x ≠ 0) (m : ℕ) (k : ℤ) :
    gz x (m + 2) k - gz x (m + 1) k - x ^ (m + 1) * gz x m (k - 1)
      = x ^ ((m : ℤ) + 2 - k) * gz x m (k - 2) := by
  have h1 := gz_pascal2 x hx (m + 1) k
  have h2 := gz_pascal1 x hx m (k - 1)
  have e1 : (((m + 1 : ℕ) : ℤ) + 1 - k) = (m : ℤ) + 2 - k := by push_cast; ring
  have e2 : k - 1 - 1 = k - 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  have hyu : x ^ ((m : ℤ) + 2 - k) * x ^ (k - 1) = x ^ (m + 1) := by
    rw [← zpow_add₀ hx, ← zpow_natCast]; congr 1; push_cast; ring
  linear_combination h1 + x ^ ((m : ℤ) + 2 - k) * h2 + gz x m (k - 1) * hyu

lemma gz_L2 (x : ℂ) (hx : x ≠ 0) (m : ℕ) (a : ℤ) :
    gz x (m + 2) a - gz x (m + 1) (a - 1) - x ^ (m + 1) * gz x m (a - 1)
      = x ^ a * gz x m a := by
  have h1 := gz_pascal1 x hx (m + 1) a
  have h2 := gz_pascal2 x hx m a
  have hyu : x ^ a * x ^ ((m : ℤ) + 1 - a) = x ^ (m + 1) := by
    rw [← zpow_add₀ hx, ← zpow_natCast]; congr 1; push_cast; ring
  linear_combination h1 + x ^ a * h2 + gz x m (a - 1) * hyu


/-- The exponent `j (5 j + 1) / 2` of Schur's identity. -/
def ex (j : ℤ) : ℤ := j * (5 * j + 1) / 2

lemma ex_succ (j : ℤ) : ex (j + 1) = ex j + 5 * j + 3 := by
  unfold ex
  have h1 : (j * (5 * j + 1)) % 2 = 0 := by
    rw [Int.mul_emod]
    rcases Int.emod_two_eq_zero_or_one j with h | h
    · rw [h]; simp
    · have h' : (5 * j + 1) % 2 = 0 := by omega
      rw [h']; simp
  have h2 : (j + 1) * (5 * (j + 1) + 1) = j * (5 * j + 1) + 10 * j + 6 := by ring
  rw [h2]
  generalize j * (5 * j + 1) = A at h1 ⊢
  omega

/-- Term of Schur's closed form. -/
noncomputable def tt (x : ℂ) (n : ℕ) (j : ℤ) : ℂ :=
  (-1 : ℂ) ^ j * x ^ (ex j) * gz x n (((n : ℤ) - 5 * j) / 2)

lemma tt_support (x : ℂ) (n : ℕ) (j : ℤ) (hj : j < -(n : ℤ) ∨ (n : ℤ) < j) : tt x n j = 0 := by
  unfold tt
  have : gz x n (((n : ℤ) - 5 * j) / 2) = 0 := by
    rcases hj with h | h
    · exact gz_gt x n (by omega)
    · exact gz_neg x n (by omega)
  rw [this]; simp

/-- Schur's closed form. -/
noncomputable def TT (x : ℂ) (n : ℕ) : ℂ := ∑ j ∈ Finset.Icc (-(n : ℤ)) n, tt x n j

lemma TT_ext (x : ℂ) (n N : ℕ) (h : n ≤ N) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) N, tt x n j = TT x n := by
  unfold TT
  symm
  apply Finset.sum_subset
  · intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    omega
  · intro j _ hj
    apply tt_support
    rw [Finset.mem_Icc] at hj
    omega

lemma sum_pairs (h : ℤ → ℂ) (N : ℕ) (r : ℤ) (hr : r = 0 ∨ r = 1)
    (hpair : ∀ j, j % 2 = r → h j + h (j + 1) = 0)
    (hsupp : ∀ j, (j < -(N : ℤ) ∨ (N : ℤ) < j) → h j = 0) :
    ∑ j ∈ Finset.Icc (-(N : ℤ)) N, h j = 0 := by
  obtain ⟨a, ha1, ha2⟩ : ∃ a : ℤ, a % 2 = r ∧ (a = -(N : ℤ) - 1 ∨ a = -(N : ℤ) - 2) := by
    by_cases hc : (-(N : ℤ) - 1) % 2 = r
    · exact ⟨_, hc, Or.inl rfl⟩
    · by_cases hr : (-(N : ℤ) - 2) % 2 = r
      · exact ⟨_, hr, Or.inr rfl⟩
      · exfalso; omega
  have key : ∀ q : ℕ, ∑ i ∈ Finset.range (2 * q), h (a + i) = 0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      have e0 : 2 * (q + 1) = 2 * q + 1 + 1 := by ring
      rw [e0, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hp := hpair (a + ((2 * q : ℕ) : ℤ)) (by push_cast; omega)
      have e : a + ((2 * q + 1 : ℕ) : ℤ) = (a + ((2 * q : ℕ) : ℤ)) + 1 := by push_cast; ring
      rw [e]
      simpa using hp
  have hsub : Finset.Icc (-(N : ℤ)) N ⊆
      (Finset.range (2 * (N + 2))).image (fun i : ℕ => a + (i : ℤ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_image]
    refine ⟨(j - a).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
  rw [Finset.sum_subset hsub, Finset.sum_image, key]
  · intro i _ i' _ hii; simpa using hii
  · intro j hj hnot
    apply hsupp
    rw [Finset.mem_image] at hj
    obtain ⟨i, _, rfl⟩ := hj
    rw [Finset.mem_Icc] at hnot
    omega


lemma pair_identity (x : ℂ) (hx : x ≠ 0) (m : ℕ) (j : ℤ) (hj : ((m : ℤ) + 2 - 5 * j) % 2 = 1) :
    (tt x (m + 2) j - tt x (m + 1) j - x ^ (m + 1) * tt x m j)
      + (tt x (m + 2) (j + 1) - tt x (m + 1) (j + 1) - x ^ (m + 1) * tt x m (j + 1)) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (m : ℤ) + 2 - 5 * j = 2 * k + 1 := ⟨((m : ℤ) + 2 - 5 * j) / 2, by omega⟩
  have d1 : (((m + 2 : ℕ) : ℤ) - 5 * j) / 2 = k := by push_cast; omega
  have d2 : (((m + 1 : ℕ) : ℤ) - 5 * j) / 2 = k := by push_cast; omega
  have d3 : (((m : ℕ) : ℤ) - 5 * j) / 2 = k - 1 := by omega
  have d4 : (((m + 2 : ℕ) : ℤ) - 5 * (j + 1)) / 2 = k - 2 := by push_cast; omega
  have d5 : (((m + 1 : ℕ) : ℤ) - 5 * (j + 1)) / 2 = k - 3 := by push_cast; omega
  have d6 : (((m : ℕ) : ℤ) - 5 * (j + 1)) / 2 = k - 3 := by omega
  unfold tt
  rw [d1, d2, d3, d4, d5, d6]
  have L1 := gz_L1 x hx m k
  have L2 := gz_L2 x hx m (k - 2)
  have e3 : k - 2 - 1 = k - 3 := by ring
  rw [e3] at L2
  have hsign : (-1 : ℂ) ^ (j + 1) = -((-1 : ℂ) ^ j) := by
    rw [zpow_add_one₀ (by norm_num)]; ring
  have hexp : x ^ (ex j) * x ^ ((m : ℤ) + 2 - k) = x ^ (ex (j + 1)) * x ^ (k - 2) := by
    rw [← zpow_add₀ hx, ← zpow_add₀ hx, ex_succ]
    congr 1
    omega
  rw [hsign]
  linear_combination ((-1 : ℂ) ^ j * x ^ (ex j)) * L1 - ((-1 : ℂ) ^ j * x ^ (ex (j + 1))) * L2
    + ((-1 : ℂ) ^ j * gz x m (k - 2)) * hexp

lemma TT_rec (x : ℂ) (hx : x ≠ 0) (m : ℕ) : TT x (m + 2) = TT x (m + 1) + x ^ (m + 1) * TT x m := by
  have e2 := TT_ext x (m + 2) (m + 2) le_rfl
  have e1 := TT_ext x (m + 1) (m + 2) (by omega)
  have e0 := TT_ext x m (m + 2) (by omega)
  have hS : ∑ j ∈ Finset.Icc (-((m + 2 : ℕ) : ℤ)) ((m + 2 : ℕ) : ℤ),
      (tt x (m + 2) j - tt x (m + 1) j - x ^ (m + 1) * tt x m j) = 0 := by
    apply sum_pairs _ (m + 2) (((m : ℤ) + 1) % 2) (by omega)
    · intro j hj
      apply pair_identity x hx m j
      omega
    · intro j hj
      rw [tt_support x (m + 2) j hj, tt_support x (m + 1) j (by push_cast at hj ⊢; omega),
        tt_support x m j (by push_cast at hj ⊢; omega)]
      simp
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e2, e1, e0] at hS
  linear_combination hS


lemma TT_one (x : ℂ) : TT x 1 = 1 := by
  have h : Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  unfold TT
  rw [h]
  have a1 : tt x 1 (-1) = 0 := by
    unfold tt
    rw [gz_gt x 1 (by norm_num)]; simp
  have a2 : tt x 1 1 = 0 := by
    unfold tt
    rw [gz_neg x 1 (by norm_num)]; simp
  have a0 : tt x 1 0 = 1 := by
    unfold tt ex
    have : gz x 1 ((((1 : ℕ) : ℤ) - 5 * 0) / 2) = 1 := by
      have : ((((1 : ℕ) : ℤ) - 5 * 0) / 2) = ((0 : ℕ) : ℤ) := by norm_num
      rw [this, gz_nat, gb_zero_right]
    rw [this]; simp
  simp [Finset.sum_insert, a1, a2, a0]

lemma TT_two (x : ℂ) : TT x 2 = 1 + x := by
  have h : Finset.Icc (-((2 : ℕ) : ℤ)) ((2 : ℕ) : ℤ) = {-2, -1, 0, 1, 2} := by decide
  unfold TT
  rw [h]
  have a1 : tt x 2 (-1) = 0 := by
    unfold tt
    rw [gz_gt x 2 (by norm_num)]; simp
  have a2 : tt x 2 1 = 0 := by
    unfold tt
    rw [gz_neg x 2 (by norm_num)]; simp
  have a3 : tt x 2 (-2) = 0 := by
    unfold tt
    rw [gz_gt x 2 (by norm_num)]; simp
  have a4 : tt x 2 2 = 0 := by
    unfold tt
    rw [gz_neg x 2 (by norm_num)]; simp
  have a0 : tt x 2 0 = 1 + x := by
    unfold tt ex
    have : gz x 2 ((((2 : ℕ) : ℤ) - 5 * 0) / 2) = 1 + x := by
      have : ((((2 : ℕ) : ℤ) - 5 * 0) / 2) = ((1 : ℕ) : ℤ) := by norm_num
      rw [this, gz_nat]
      simp [gb]
    rw [this]; simp
  simp [Finset.sum_insert, a1, a2, a3, a4, a0]

lemma num_eq_TT (x : ℂ) (hx : x ≠ 0) : ∀ m : ℕ, rrcfNum 1 x m = TT x (m + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [rrcfNum, TT_one]
    | 1, _ => simp [rrcfNum, TT_two]
    | k + 2, ih =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hr := TT_rec x hx (k + 1)
      show rrcfNum 1 x (k + 1) + 1 * x ^ (k + 2) * rrcfNum 1 x k = TT x (k + 2 + 1)
      rw [h1, h0]
      have : TT x (k + 2 + 1) = TT x (k + 1 + 2) := rfl
      rw [this, hr]; ring

lemma num_zero (x : ℂ) (m : ℕ) (hx : IsPrimitiveRoot x (m + 1))
    (hn : (m + 1) % 5 = 2 ∨ (m + 1) % 5 = 3) : rrcfNum 1 x m = 0 := by
  have hx0 : x ≠ 0 := hx.ne_zero (by omega)
  rw [num_eq_TT x hx0 m]
  unfold TT
  apply Finset.sum_eq_zero
  intro j _
  unfold tt
  have : gz x (m + 1) ((((m + 1 : ℕ) : ℤ) - 5 * j) / 2) = 0 := by
    generalize hK : (((m + 1 : ℕ) : ℤ) - 5 * j) / 2 = K
    have hK' : (m : ℤ) + 1 - 5 * j = 2 * K ∨ (m : ℤ) + 1 - 5 * j = 2 * K + 1 := by
      push_cast at hK; omega
    rcases lt_trichotomy K 0 with h | h | h
    · exact gz_neg x _ h
    · exfalso; subst h; omega
    · by_cases hKm : (m : ℤ) + 1 ≤ K
      · rcases eq_or_lt_of_le hKm with h2 | h2
        · exfalso; omega
        · exact gz_gt x _ (by omega)
      · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt h)
        cases i with
        | zero => omega
        | succ i =>
          rw [gz_nat]
          exact gb_root x m hx i (by omega)
  rw [this]; simp

lemma det_ne (x : ℂ) (hx : x ≠ 0) : ∀ k : ℕ,
    rrcfNum 1 x (k + 1) * rrcfDen 1 x k - rrcfNum 1 x k * rrcfDen 1 x (k + 1) ≠ 0 := by
  intro k
  induction k with
  | zero => simp [rrcfNum, rrcfDen, hx]
  | succ k ih =>
    have e : rrcfNum 1 x (k + 1 + 1) * rrcfDen 1 x (k + 1) - rrcfNum 1 x (k + 1) * rrcfDen 1 x (k + 1 + 1)
        = -(x ^ (k + 2)) * (rrcfNum 1 x (k + 1) * rrcfDen 1 x k - rrcfNum 1 x k * rrcfDen 1 x (k + 1)) := by
      show (rrcfNum 1 x (k + 1) + 1 * x ^ (k + 2) * rrcfNum 1 x k) * rrcfDen 1 x (k + 1)
          - rrcfNum 1 x (k + 1) * (rrcfDen 1 x (k + 1) + 1 * x ^ (k + 2) * rrcfDen 1 x k) = _
      ring
    rw [e]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hx)) ih

lemma den_ne (x : ℂ) (m : ℕ) (hx : IsPrimitiveRoot x (m + 1))
    (hn : (m + 1) % 5 = 2 ∨ (m + 1) % 5 = 3) : rrcfDen 1 x m ≠ 0 := by
  have hx0 : x ≠ 0 := hx.ne_zero (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h0 := num_zero x (k + 1) hx hn
  have hd := det_ne x hx0 k
  intro hB
  apply hd
  rw [h0, hB]; ring

end RRCFAux

theorem solution (m : ℕ) (x : ℂ) (hn : (m + 1) % 5 = 2 ∨ (m + 1) % 5 = 3)
    (hx : IsPrimitiveRoot x (m + 1)) :
    RamanujanLostNotebook.PartV.rrcfNum 1 x m = 0 ∧
      RamanujanLostNotebook.PartV.rrcfDen 1 x m ≠ 0 :=
  ⟨RRCFAux.num_zero x m hx hn, RRCFAux.den_ne x m hx hn⟩
