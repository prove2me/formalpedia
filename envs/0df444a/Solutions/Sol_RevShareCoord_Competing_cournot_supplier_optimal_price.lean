-- Prove2me | solution 1 for RevShareCoord.Competing.cournot_supplier_optimal_price
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:02:16.274229+00:00
-- url     : https://prove2.me/submissions/88f53873-5021-435d-bf66-3dedac44719e

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot



namespace RevShareCoord.Competing

open Finset

lemma cr_card {n : ℕ} (i : Fin n) : ((univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
  rw [Finset.card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
  push_cast [this]; ring

lemma cr_sum_erase_update {n : ℕ} (q : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    ∑ k ∈ univ.erase i, Function.update q i x k = ∑ k ∈ univ.erase i, q k :=
  Finset.sum_congr rfl (fun k hk => Function.update_of_ne (Finset.ne_of_mem_erase hk) _ _)

lemma cr_profit {n : ℕ} (β : ℝ) (w q : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    retailerProfit (cournotRevenue β) 1 w (Function.update q i x) i =
      x * (1 - x - β * ∑ k ∈ univ.erase i, q k) - w i * x := by
  simp only [retailerProfit, cournotRevenue, cr_sum_erase_update, Function.update_self]; ring

lemma cr_profit0 {n : ℕ} (β : ℝ) (w q : Fin n → ℝ) (i : Fin n) :
    retailerProfit (cournotRevenue β) 1 w q i =
      q i * (1 - q i - β * ∑ k ∈ univ.erase i, q k) - w i * q i := by
  simp only [retailerProfit, cournotRevenue]; ring

lemma cr_sym_nash {n : ℕ} (β w b : ℝ) (hb : 0 ≤ b) (hrel : b * (2 + β * ((n : ℝ) - 1)) = 1 - w) :
    IsNashEquilibrium (cournotRevenue β) 1 (fun _ : Fin n => w) (fun _ => b) := by
  refine ⟨fun _ => hb, fun i x _ => ?_⟩
  rw [cr_profit, cr_profit0]
  simp only [Finset.sum_const, nsmul_eq_mul, cr_card]
  nlinarith [sq_nonneg (x - b)]

lemma cr_cases {n : ℕ} (β w : ℝ) (q : Fin n → ℝ)
    (hN : IsNashEquilibrium (cournotRevenue β) 1 (fun _ => w) q) (i : Fin n) :
    (0 < q i ∧ 2 * q i = 1 - w - β * ∑ k ∈ univ.erase i, q k) ∨
      (q i = 0 ∧ 1 - w - β * ∑ k ∈ univ.erase i, q k ≤ 0) := by
  set A := 1 - w - β * ∑ k ∈ univ.erase i, q k with hA
  have hq := hN.1 i
  have key : ∀ x, 0 ≤ x → x * (A - x) ≤ q i * (A - q i) := by
    intro x hx
    have := hN.2 i x hx
    rw [cr_profit, cr_profit0] at this
    simp only [hA]; linarith
  by_cases h : 0 ≤ A
  · have := key (A / 2) (by linarith)
    have e : q i = A / 2 := by nlinarith [sq_nonneg (q i - A / 2)]
    rcases eq_or_lt_of_le hq with h0 | h0
    · right; refine ⟨h0.symm, ?_⟩; rw [← h0] at e; linarith
    · left; exact ⟨h0, by linarith⟩
  · have := key 0 le_rfl
    right; refine ⟨by nlinarith, by linarith⟩

lemma cr_den1 {n : ℕ} (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) : 0 < 2 + β * ((n : ℝ) - 1) := by
  have : (0:ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hβ0 this]

lemma cr_den2 {n : ℕ} (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) : 0 < 2 + 2 * β * ((n : ℝ) - 1) := by
  have : (0:ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hβ0 this]

lemma cr_nash_eq {n : ℕ} (β w : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hw : w < 1) (q : Fin n → ℝ)
    (hN : IsNashEquilibrium (cournotRevenue β) 1 (fun _ => w) q) :
    q = fun _ => cournotQN β n w := by
  set S := ∑ k, q k with hS
  have hE : ∀ i, ∑ k ∈ univ.erase i, q k = S - q i := fun i =>
    Finset.sum_erase_eq_sub (mem_univ i)
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun k _ => hN.1 k)
  -- every coordinate is positive
  have hall : ∀ i, (2 - β) * q i = 1 - w - β * S := by
    intro i
    rcases cr_cases β w q hN i with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [hE] at h1; linarith
    · exfalso
      rw [hE, h0, sub_zero] at h1
      have hz : ∀ j, q j = 0 := by
        intro j
        rcases cr_cases β w q hN j with ⟨g0, g1⟩ | ⟨g0, _⟩
        · rw [hE] at g1; nlinarith
        · exact g0
      have : S = 0 := by simp [hS, hz]
      rw [this] at h1; linarith
  have hconst : ∀ i, q i = (1 - w - β * S) / (2 - β) := by
    intro i; rw [eq_div_iff (by linarith)]; linarith [hall i]
  have hSn : S = n * ((1 - w - β * S) / (2 - β)) := by
    have h1 : ∑ k, q k = ∑ _k : Fin n, (1 - w - β * S) / (2 - β) :=
      Finset.sum_congr rfl (fun k _ => hconst k)
    have h2 : ∑ _k : Fin n, (1 - w - β * S) / (2 - β) = n * ((1 - w - β * S) / (2 - β)) := by simp
    exact hS.trans (h1.trans h2)
  funext i
  rw [hconst i]
  unfold cournotQN
  have h2 : (2 - β) ≠ 0 := by linarith
  have h3 := cr_den1 (n := n) β hβ0 hβ1
  rw [div_eq_div_iff h2 h3.ne']
  field_simp at hSn
  nlinarith [hSn]

lemma cr_nash_zero {n : ℕ} (β w : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hw : 1 ≤ w) (q : Fin n → ℝ)
    (hN : IsNashEquilibrium (cournotRevenue β) 1 (fun _ => w) q) :
    q = fun _ => 0 := by
  funext i
  have hnn : 0 ≤ ∑ k ∈ univ.erase i, q k := Finset.sum_nonneg (fun k _ => hN.1 k)
  rcases cr_cases β w q hN i with ⟨h0, h1⟩ | ⟨h0, _⟩
  · nlinarith [mul_nonneg hβ0 hnn]
  · exact h0

lemma cr_sys {n : ℕ} (β c : ℝ) (q : Fin n → ℝ) :
    systemProfit (cournotRevenue β) c q =
      (1 - c) * ∑ k, q k - (1 - β) * ∑ k, q k ^ 2 - β * (∑ k, q k) ^ 2 := by
  have h : ∀ i, cournotRevenue β i q = q i - (1 - β) * q i ^ 2 - β * (∑ k, q k) * q i := by
    intro i; simp only [cournotRevenue]; rw [Finset.sum_erase_eq_sub (mem_univ i)]; ring
  simp only [systemProfit, h, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma cr_sq {n : ℕ} (q : Fin n → ℝ) (a : ℝ) :
    ∑ k, (q k - a) ^ 2 = ∑ k, q k ^ 2 - 2 * a * ∑ k, q k + n * a ^ 2 := by
  have h : ∀ k, (q k - a) ^ 2 = q k ^ 2 - 2 * a * q k + a ^ 2 := fun k => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma cr_sys_gap {n : ℕ} (β c : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (q : Fin n → ℝ) :
    systemProfit (cournotRevenue β) c q =
      systemProfit (cournotRevenue β) c (fun _ : Fin n => cournotQI β n c)
        - (1 - β) * ∑ k, (q k - cournotQI β n c) ^ 2
        - β * (∑ k, q k - n * cournotQI β n c) ^ 2 := by
  have hD := cr_den2 (n := n) β hβ0 hβ1
  have hrel : cournotQI β n c * (2 + 2 * β * ((n : ℝ) - 1)) = 1 - c := by
    unfold cournotQI; rw [div_mul_cancel₀ _ hD.ne']
  rw [cr_sys, cr_sys, cr_sq]
  simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  set a := cournotQI β n c
  linear_combination (↑n * a - ∑ k, q k) * hrel

theorem cournot_coordinating_price_core {n : ℕ} (β c : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc0 : 0 < c) (hc1 : c < 1) :
    (IsMaxOn (systemProfit (cournotRevenue β) c) {q : Fin n → ℝ | ∀ i, 0 ≤ q i}
        (fun _ => cournotQI β n c) ∧
      ∀ q ∈ {q : Fin n → ℝ | ∀ i, 0 ≤ q i},
        IsMaxOn (systemProfit (cournotRevenue β) c) {q : Fin n → ℝ | ∀ i, 0 ≤ q i} q →
          q = fun _ => cournotQI β n c) ∧
    (∀ (q : Fin n → ℝ) (i j : Fin n), j ≠ i →
      HasDerivAt (fun t => cournotRevenue β j (Function.update q i t)) (-β * q j) (q i)) ∧
    (∀ i : Fin n, c - ∑ j ∈ univ.erase i, (-β * cournotQI β n c) = cournotWI β n c) ∧
    IsNashEquilibrium (cournotRevenue β) 1 (fun _ : Fin n => cournotWI β n c)
      (fun _ => cournotQI β n c) := by
  have hD := cr_den2 (n := n) β hβ0 hβ1
  have ha : 0 ≤ cournotQI β n c := by unfold cournotQI; exact div_nonneg (by linarith) hD.le
  refine ⟨⟨fun q _ => ?_, fun q hq hmax => ?_⟩, ?_, ?_, ?_⟩
  · show systemProfit (cournotRevenue β) c q ≤ _
    rw [cr_sys_gap β c hβ0 hβ1 q]
    have : 0 ≤ ∑ k, (q k - cournotQI β n c) ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    nlinarith [mul_nonneg hβ0 (sq_nonneg (∑ k, q k - n * cournotQI β n c))]
  · have h1 : systemProfit (cournotRevenue β) c (fun _ => cournotQI β n c) ≤
        systemProfit (cournotRevenue β) c q := hmax (show ∀ i, 0 ≤ cournotQI β n c from fun _ => ha)
    rw [cr_sys_gap β c hβ0 hβ1 q] at h1
    have hs : 0 ≤ ∑ k, (q k - cournotQI β n c) ^ 2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have h0 : ∑ k, (q k - cournotQI β n c) ^ 2 = 0 := by
      nlinarith [mul_nonneg hβ0 (sq_nonneg (∑ k, q k - n * cournotQI β n c))]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)] at h0
    funext i
    have := h0 i (mem_univ i)
    have : q i - cournotQI β n c = 0 := by simpa using this
    linarith
  · intro q i j hji
    have hfun : (fun t => cournotRevenue β j (Function.update q i t)) =
        fun t => q j * ((1 - q j) - β * (t + ∑ k ∈ (univ.erase j).erase i, q k)) := by
      funext t
      have hi : i ∈ univ.erase j := Finset.mem_erase.mpr ⟨fun h => hji h.symm, mem_univ i⟩
      simp only [cournotRevenue, Function.update_of_ne hji]
      rw [← Finset.add_sum_erase _ _ hi, Function.update_self]
      rw [Finset.sum_congr rfl (fun k hk => Function.update_of_ne (Finset.ne_of_mem_erase hk) t q)]
    rw [hfun]
    have := ((((hasDerivAt_id (q i)).add_const (∑ k ∈ (univ.erase j).erase i, q k)).const_mul
      β).const_sub (1 - q j)).const_mul (q j)
    exact this.congr_deriv (by ring)
  · intro i
    rw [Finset.sum_const, nsmul_eq_mul, cr_card]
    unfold cournotWI cournotQI; ring
  · apply cr_sym_nash _ _ _ ha
    unfold cournotWI
    have hrel : cournotQI β n c * (2 + 2 * β * ((n : ℝ) - 1)) = 1 - c := by
      unfold cournotQI; rw [div_mul_cancel₀ _ hD.ne']
    have e : β * ((n:ℝ) - 1) * (1 - c) / (2 + 2 * β * ((n:ℝ) - 1)) =
        β * ((n:ℝ) - 1) * cournotQI β n c := by unfold cournotQI; ring
    rw [e]; linear_combination hrel

theorem cournot_wI_monotone_core (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∀ n : ℕ, 2 ≤ n → StrictMonoOn (fun β => cournotWI β n c) (Set.Ico 0 1)) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ m k : ℕ, 1 ≤ m → m < k →
        cournotWI β m c < cournotWI β k c := by
  refine ⟨fun n hn a ha b hb hab => ?_, fun β hβ0 hβ1 m k hm hmk => ?_⟩
  · have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
    simp only [cournotWI]
    have h1 : 0 < 2 + 2 * a * ((n:ℝ) - 1) := by nlinarith [ha.1]
    have h2 : 0 < 2 + 2 * b * ((n:ℝ) - 1) := by nlinarith [hb.1]
    rw [add_lt_add_iff_left]
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith [mul_pos (mul_pos (sub_pos.mpr hab) (by linarith : (0:ℝ) < n - 1))
      (by linarith : (0:ℝ) < 1 - c)]
  · have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hmk' : (m:ℝ) < k := by exact_mod_cast hmk
    simp only [cournotWI]
    have h1 : 0 < 2 + 2 * β * ((m:ℝ) - 1) := by nlinarith
    have h2 : 0 < 2 + 2 * β * ((k:ℝ) - 1) := by nlinarith
    rw [add_lt_add_iff_left]
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith [mul_pos (mul_pos hβ0 (sub_pos.mpr hmk')) (by linarith : (0:ℝ) < 1 - c)]

lemma cr_supp {n : ℕ} (β c w : ℝ) (q : Fin n → ℝ) :
    supplierProfit (cournotRevenue β) c 1 (fun _ => w) q = (w - c) * ∑ k, q k := by
  simp only [supplierProfit, sub_self, zero_mul, zero_add, ← Finset.mul_sum]; ring

theorem cournot_supplier_optimal_price_core {n : ℕ} (β c : ℝ) (hn : 1 ≤ n) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hc0 : 0 < c) (hc1 : c < 1) :
    IsNashEquilibrium (cournotRevenue β) 1 (fun _ : Fin n => (1 + c) / 2)
        (fun _ => cournotQN β n ((1 + c) / 2)) ∧
      (∀ w : ℝ, 0 < w → ∀ q : Fin n → ℝ,
        IsNashEquilibrium (cournotRevenue β) 1 (fun _ => w) q →
          supplierProfit (cournotRevenue β) c 1 (fun _ => w) q ≤
              supplierProfit (cournotRevenue β) c 1 (fun _ : Fin n => (1 + c) / 2)
                (fun _ => cournotQN β n ((1 + c) / 2)) ∧
            (w ≠ (1 + c) / 2 →
              supplierProfit (cournotRevenue β) c 1 (fun _ => w) q <
                supplierProfit (cournotRevenue β) c 1 (fun _ : Fin n => (1 + c) / 2)
                  (fun _ => cournotQN β n ((1 + c) / 2)))) ∧
      (1 + c) / 2 - cournotWI β n c = (1 - c) / (2 + 2 * β * ((n : ℝ) - 1)) := by
  have hD := cr_den1 (n := n) β hβ0 hβ1
  have hD2 := cr_den2 (n := n) β hβ0 hβ1
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hsym : ∀ w, ∑ _k : Fin n, cournotQN β n w = n * cournotQN β n w := by
    intro w; simp [Finset.sum_const, card_univ]
  have htarget : supplierProfit (cournotRevenue β) c 1 (fun _ : Fin n => (1 + c) / 2)
      (fun _ => cournotQN β n ((1 + c) / 2)) = n * (1 - c) ^ 2 / (4 * (2 + β * ((n:ℝ) - 1))) := by
    rw [cr_supp, hsym]; unfold cournotQN; field_simp; ring
  refine ⟨cr_sym_nash _ _ _ ?_ ?_, fun w hw q hN => ?_, ?_⟩
  · unfold cournotQN; exact div_nonneg (by linarith) hD.le
  · unfold cournotQN; field_simp
  · rw [htarget]
    rcases lt_or_ge w 1 with hw1 | hw1
    · rw [cr_nash_eq β w hβ0 hβ1 hw1 q hN, cr_supp, hsym]
      have key : n * (1 - c) ^ 2 / (4 * (2 + β * ((n:ℝ) - 1))) - (w - c) * (n * cournotQN β n w)
          = n * (w - (1 + c) / 2) ^ 2 / (2 + β * ((n:ℝ) - 1)) := by
        unfold cournotQN; field_simp; ring
      refine ⟨?_, fun hne => ?_⟩
      · have : 0 ≤ n * (w - (1 + c) / 2) ^ 2 / (2 + β * ((n:ℝ) - 1)) := by positivity
        linarith
      · have : 0 < n * (w - (1 + c) / 2) ^ 2 / (2 + β * ((n:ℝ) - 1)) := by
          apply div_pos _ hD
          apply mul_pos (by linarith)
          exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne)))
        linarith
    · rw [cr_nash_zero β w hβ0 hβ1 hw1 q hN, cr_supp]
      have : 0 < n * (1 - c) ^ 2 / (4 * (2 + β * ((n:ℝ) - 1))) := by
        apply div_pos _ (by linarith)
        apply mul_pos (by linarith); nlinarith
      simp only [Finset.sum_const_zero, mul_zero]
      exact ⟨this.le, fun _ => this⟩
  · unfold cournotWI
    rw [eq_div_iff hD2.ne', sub_mul, add_mul, div_mul_cancel₀ _ hD2.ne']; ring

theorem cournot_efficiency_core {n : ℕ} (β c : ℝ) (hn : 1 ≤ n) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (qN qI : Fin n → ℝ)
    (hN : IsNashEquilibrium (cournotRevenue β) 1 (fun _ => (1 + c) / 2) qN)
    (hI0 : ∀ i, 0 ≤ qI i)
    (hI : IsMaxOn (systemProfit (cournotRevenue β) c) {q : Fin n → ℝ | ∀ i, 0 ≤ q i} qI) :
    systemProfit (cournotRevenue β) c qN / systemProfit (cournotRevenue β) c qI =
      1 - 1 / (2 + β * ((n : ℝ) - 1)) ^ 2 := by
  have hD := cr_den1 (n := n) β hβ0 hβ1
  have hD2 := cr_den2 (n := n) β hβ0 hβ1
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  rw [cr_nash_eq β _ hβ0 hβ1 (by linarith) qN hN,
    (cournot_coordinating_price_core (n := n) β c hβ0 hβ1 hc0 hc1).1.2 qI hI0 hI]
  rw [cr_sys, cr_sys]
  simp only [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold cournotQN cournotQI
  have hc' : (1 - c) ≠ 0 := by linarith
  have hE : (1 + β * ((n:ℝ) - 1)) ≠ 0 := by nlinarith
  rw [div_eq_iff]
  · field_simp; ring
  · field_simp
    intro h
    have : 0 < (n:ℝ) * (1 - c) ^ 2 := by positivity
    have hEpos : 0 < 1 + β * ((n:ℝ) - 1) := by nlinarith
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · nlinarith [mul_pos this hEpos]
    · have : (0:ℝ) < 2 ^ 2 * (1 + β * ((n:ℝ) - 1)) ^ 2 := mul_pos (by norm_num) (pow_pos hEpos 2)
      linarith
end RevShareCoord.Competing

open RevShareCoord.Competing


theorem solution {n : ℕ} (β c : ℝ) (hn : 1 ≤ n) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hc0 : 0 < c) (hc1 : c < 1) :
    IsNashEquilibrium (cournotRevenue β) 1 (fun _ : Fin n => (1 + c) / 2)
        (fun _ => cournotQN β n ((1 + c) / 2)) ∧
      (∀ w : ℝ, 0 < w → ∀ q : Fin n → ℝ,
        IsNashEquilibrium (cournotRevenue β) 1 (fun _ => w) q →
          supplierProfit (cournotRevenue β) c 1 (fun _ => w) q ≤
              supplierProfit (cournotRevenue β) c 1 (fun _ : Fin n => (1 + c) / 2)
                (fun _ => cournotQN β n ((1 + c) / 2)) ∧
            (w ≠ (1 + c) / 2 →
              supplierProfit (cournotRevenue β) c 1 (fun _ => w) q <
                supplierProfit (cournotRevenue β) c 1 (fun _ : Fin n => (1 + c) / 2)
                  (fun _ => cournotQN β n ((1 + c) / 2)))) ∧
      (1 + c) / 2 - cournotWI β n c = (1 - c) / (2 + 2 * β * ((n : ℝ) - 1)) := by
  exact cournot_supplier_optimal_price_core β c hn hβ0 hβ1 hc0 hc1
