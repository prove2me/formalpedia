-- Prove2me | solution 1 for SetCoverThreshold.SetCover.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:52:24.174749+00:00
-- url     : https://prove2.me/submissions/2808bfe5-661b-4338-92c9-a846e6b4d93f

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem

namespace SetCoverThreshold.SetCover

open Finset

lemma aux_lc_exp_bound (k : ℕ) (hk : 2 ≤ k) :
    (k : ℝ) * Real.exp (-(1:ℝ) / ((k:ℝ) - 1)) ≤ (k:ℝ) - 1 := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  set s : ℝ := (k:ℝ) - 1 with hs
  have hs1 : 1 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have h1 := Real.add_one_le_exp (1 / s)
  have h2 : Real.exp (-(1:ℝ) / s) * Real.exp (1 / s) = 1 := by
    rw [← Real.exp_add]; simp [neg_div]
  have h3 : 0 < Real.exp (-(1:ℝ) / s) := Real.exp_pos _
  have hk2 : (k:ℝ) = s + 1 := by rw [hs]; ring
  rw [hk2]
  have : s * (1 / s + 1) = 1 + s := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h1 hspos.le]

lemma aux_lc_rows (L k : ℕ) (hk : 2 ≤ k) (F : Finset (Fin L × Fin k))
    (hF : ∀ x ∈ F, ∀ y ∈ F, x.1 = y.1 → x = y) :
    ((univ.filter (fun row : Fin L → Fin k => ∃ x ∈ F, row x.1 = x.2)).card : ℝ) ≤
      (k:ℝ) ^ L * (1 - Real.exp (-(F.card : ℝ) / ((k:ℝ) - 1))) := by
  classical
  have htot := card_filter_add_card_filter_not (s := (univ : Finset (Fin L → Fin k)))
    (fun row : Fin L → Fin k => ∃ x ∈ F, row x.1 = x.2)
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at htot
  have hC : (univ.filter fun row : Fin L → Fin k => ¬ ∃ x ∈ F, row x.1 = x.2) =
      Fintype.piFinset (fun j : Fin L => univ.filter (fun i : Fin k => (j, i) ∉ F)) := by
    ext row
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, not_exists, not_and]
    constructor
    · intro h j hj
      exact h _ hj rfl
    · intro h x hx hrow
      apply h x.1
      rw [hrow]
      exact hx
  set a : Fin L → ℕ := fun j => (univ.filter (fun i : Fin k => (j, i) ∈ F)).card with ha
  have hTj : ∀ j : Fin L, (univ.filter (fun i : Fin k => (j, i) ∉ F)).card + a j = k := by
    intro j
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin k)))
      (fun i : Fin k => (j, i) ∈ F)
    rw [card_univ, Fintype.card_fin] at this
    simp only [ha]
    omega
  have ha1 : ∀ j, a j ≤ 1 := by
    intro j
    simp only [ha]
    rw [Finset.card_le_one]
    intro i hi i' hi'
    simp only [mem_filter, mem_univ, true_and] at hi hi'
    have := hF _ hi _ hi' rfl
    simpa using this
  have hsum : ∑ j, a j = F.card := by
    simp only [ha]
    have hF' : F.card = (univ.filter (fun p : Fin L × Fin k => p ∈ F)).card := by
      congr 1; ext p; simp
    rw [hF', card_filter, Fintype.sum_prod_type]
    simp only [card_filter]
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hTj' : ∀ j : Fin L, (k:ℝ) * Real.exp (-(a j : ℝ) / ((k:ℝ) - 1)) ≤
      ((univ.filter (fun i : Fin k => (j, i) ∉ F)).card : ℝ) := by
    intro j
    have h1 := hTj j
    have h2 := ha1 j
    interval_cases h : a j
    · have : (univ.filter (fun i : Fin k => (j, i) ∉ F)).card = k := by omega
      rw [this]; simp
    · have : ((univ.filter (fun i : Fin k => (j, i) ∉ F)).card : ℝ) = (k:ℝ) - 1 := by
        have : (univ.filter (fun i : Fin k => (j, i) ∉ F)).card = k - 1 := by omega
        rw [this, Nat.cast_sub (by omega)]; simp
      rw [this]
      simpa using aux_lc_exp_bound k hk
  have hCcard : (k:ℝ) ^ L * Real.exp (-(F.card : ℝ) / ((k:ℝ) - 1)) ≤
      ((univ.filter fun row : Fin L → Fin k => ¬ ∃ x ∈ F, row x.1 = x.2).card : ℝ) := by
    rw [hC, Fintype.card_piFinset]
    push_cast
    calc (k:ℝ) ^ L * Real.exp (-(F.card : ℝ) / ((k:ℝ) - 1))
        = ∏ j : Fin L, ((k:ℝ) * Real.exp (-(a j : ℝ) / ((k:ℝ) - 1))) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← Real.exp_sum]
          congr 2
          rw [← hsum]
          push_cast
          rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
      _ ≤ _ := by
          apply Finset.prod_le_prod
          · intro j _; positivity
          · intro j _; exact hTj' j
  have htot' : ((univ.filter (fun row : Fin L → Fin k => ∃ x ∈ F, row x.1 = x.2)).card : ℝ) +
      ((univ.filter fun row : Fin L → Fin k => ¬ ∃ x ∈ F, row x.1 = x.2).card : ℝ) = (k:ℝ) ^ L := by
    exact_mod_cast htot
  nlinarith

lemma aux_lc_subsets {α : Type*} [Fintype α] [DecidableEq α] (d : ℕ) :
    (univ.filter (fun F : Finset α => F.card < d)).card ≤ d * (Fintype.card α + 1) ^ d := by
  calc (univ.filter (fun F : Finset α => F.card < d)).card
      ≤ ((range d).biUnion (fun t => powersetCard t (univ : Finset α))).card := by
        apply card_le_card
        intro F hF
        simp only [mem_filter, mem_univ, true_and] at hF
        simp only [mem_biUnion, mem_range, mem_powersetCard]
        exact ⟨F.card, hF, subset_univ _, rfl⟩
    _ ≤ ∑ t ∈ range d, (powersetCard t (univ : Finset α)).card := card_biUnion_le
    _ ≤ ∑ t ∈ range d, (Fintype.card α + 1) ^ d := by
        apply sum_le_sum
        intro t ht
        rw [card_powersetCard, card_univ]
        calc (Fintype.card α).choose t ≤ (Fintype.card α) ^ t := Nat.choose_le_pow _ _
          _ ≤ (Fintype.card α + 1) ^ t := Nat.pow_le_pow_left (by omega) _
          _ ≤ (Fintype.card α + 1) ^ d :=
              Nat.pow_le_pow_right (by omega) (by simp at ht; omega)
    _ = d * (Fintype.card α + 1) ^ d := by simp

lemma aux_lc_exists (n L k d : ℕ) (hk : 2 ≤ k) (B : ℝ)
    (hB : ∀ t : ℕ, t < d → B ≤ n * Real.exp (-(t:ℝ) / ((k:ℝ) - 1)))
    (hS : ((univ.filter (fun F : Finset (Fin L × Fin k) => F.card < d)).card : ℝ) *
      Real.exp (-B) < 1) :
    ∃ g : Fin n → Fin L → Fin k, ∀ F : Finset (Fin L × Fin k),
      (∀ x ∈ F, ∀ y ∈ F, x.1 = y.1 → x = y) → F.card < d → ∃ b, ∀ x ∈ F, g b x.1 ≠ x.2 := by
  classical
  by_contra hcon
  push Not at hcon
  set S := univ.filter (fun F : Finset (Fin L × Fin k) =>
    (∀ x ∈ F, ∀ y ∈ F, x.1 = y.1 → x = y) ∧ F.card < d) with hSdef
  set A : Finset (Fin L × Fin k) → Finset (Fin L → Fin k) := fun F =>
    univ.filter (fun row : Fin L → Fin k => ∃ x ∈ F, row x.1 = x.2) with hA
  have hsub : (univ : Finset (Fin n → Fin L → Fin k)) ⊆
      S.biUnion (fun F => Fintype.piFinset (fun _ : Fin n => A F)) := by
    intro g _
    obtain ⟨F, hF1, hF2, hF3⟩ := hcon g
    simp only [mem_biUnion, Fintype.mem_piFinset]
    refine ⟨F, ?_, ?_⟩
    · simp only [hSdef, mem_filter, mem_univ, true_and]
      exact ⟨hF1, hF2⟩
    · intro b
      simp only [hA, mem_filter, mem_univ, true_and]
      exact hF3 b
  have hcard2 := (card_le_card hsub).trans card_biUnion_le
  rw [card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin] at hcard2
  simp only [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin] at hcard2
  have hreal : ((k:ℝ)^L)^n ≤ ∑ F ∈ S, (((A F).card : ℝ))^n := by exact_mod_cast hcard2
  have hterm : ∀ F ∈ S, (((A F).card : ℝ))^n ≤ ((k:ℝ)^L)^n * Real.exp (-B) := by
    intro F hF
    simp only [hSdef, mem_filter, mem_univ, true_and] at hF
    have h1 := aux_lc_rows L k hk F hF.1
    set q := Real.exp (-(F.card : ℝ) / ((k:ℝ) - 1)) with hqdef
    have hq : B ≤ n * q := hB _ hF.2
    have hkL : 0 < (k:ℝ)^L := by positivity
    have h1q : 0 ≤ 1 - q := by
      have : (0:ℝ) ≤ (A F).card := Nat.cast_nonneg _
      by_contra hneg
      push Not at hneg
      have : (k:ℝ)^L * (1 - q) < 0 := mul_neg_of_pos_of_neg hkL hneg
      linarith
    calc (((A F).card : ℝ))^n ≤ ((k:ℝ)^L * (1 - q))^n :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h1 n
      _ = ((k:ℝ)^L)^n * (1-q)^n := mul_pow _ _ _
      _ ≤ ((k:ℝ)^L)^n * (Real.exp (-q))^n := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply pow_le_pow_left₀ h1q
          have := Real.add_one_le_exp (-q); linarith
      _ = ((k:ℝ)^L)^n * Real.exp (-(n * q)) := by
          rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ ((k:ℝ)^L)^n * Real.exp (-B) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr; linarith
  have hsum := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul] at hsum
  have hSle : (S.card : ℝ) ≤
      ((univ.filter (fun F : Finset (Fin L × Fin k) => F.card < d)).card : ℝ) := by
    exact_mod_cast card_le_card (by
      intro F hF
      simp only [hSdef, mem_filter, mem_univ, true_and] at hF ⊢
      exact hF.2)
  have hkLn : 0 < ((k:ℝ)^L)^n := by positivity
  have h2 : (S.card : ℝ) * Real.exp (-B) < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hSle (Real.exp_pos _).le) hS
  have h3 : ((k:ℝ)^L)^n * ((S.card : ℝ) * Real.exp (-B)) < ((k:ℝ)^L)^n := by
    calc ((k:ℝ)^L)^n * ((S.card : ℝ) * Real.exp (-B)) < ((k:ℝ)^L)^n * 1 :=
          mul_lt_mul_of_pos_left h2 hkLn
      _ = _ := mul_one _
  have h4 : (S.card : ℝ) * (((k:ℝ)^L)^n * Real.exp (-B)) =
      ((k:ℝ)^L)^n * ((S.card : ℝ) * Real.exp (-B)) := by ring
  linarith

lemma aux_lc_ev (c : ℝ) : ∀ᶠ x : ℝ in Filter.atTop,
    9 ≤ Real.log x ∧ (Real.logb 2 x) ^ c + 1 ≤ x / 2 := by
  have h1 := Real.tendsto_log_atTop.eventually_ge_atTop 9
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 := (isLittleO_log_rpow_rpow_atTop c one_pos).bound
    (show (0:ℝ) < (Real.log 2) ^ c / 4 by positivity)
  filter_upwards [h1, h2, Filter.eventually_ge_atTop (4:ℝ)] with x hx1 hx2 hx4
  refine ⟨hx1, ?_⟩
  have hlx : 0 ≤ Real.log x := by linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlx _), Real.rpow_one,
    Real.norm_of_nonneg (by linarith)] at hx2
  have hpos : 0 < (Real.log 2) ^ c := Real.rpow_pos_of_pos hl2 _
  rw [Real.logb, Real.div_rpow hlx hl2.le]
  have : (Real.log x) ^ c / (Real.log 2) ^ c ≤ x / 4 := by
    rw [div_le_iff₀ hpos]; linarith
  linarith

lemma aux_lc_main (m L k : ℕ) (hlog : 9 ≤ Real.log m) (hLm : (L:ℝ) + 1 ≤ (m:ℝ) / 2)
    (hk : 2 ≤ k) (hkm : (k : ℝ) < Real.log m / (3 * Real.log (Real.log m))) :
    Nonempty (PartitionSystem m L k ⌈(1 - 2 / (k : ℝ)) * k * Real.log m⌉₊) := by
  set ℓ := Real.log m with hℓ
  set d := ⌈(1 - 2 / (k : ℝ)) * k * ℓ⌉₊ with hd
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k:ℝ) ≠ 0 := by positivity
  have hkk : (1 - 2 / (k : ℝ)) * k = k - 2 := by field_simp
  have hL0 : (0:ℝ) ≤ L := Nat.cast_nonneg _
  have hm_pos : (0:ℝ) < m := by linarith
  have hL2 : 2 * (L + 1) ≤ m := by
    have : ((2 * (L + 1) : ℕ) : ℝ) ≤ (m : ℝ) := by push_cast; linarith
    exact_mod_cast this
  set n := m - (L + 1) with hn
  have hn' : (m:ℝ) / 2 ≤ (n:ℝ) := by
    rw [hn, Nat.cast_sub (by omega)]; push_cast; linarith
  have hexp2 : Real.exp 2 < 9 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  have hℓpos : 0 < ℓ := by linarith
  have hlogℓ : 2 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le hℓpos]; linarith
  have h3log : 0 < 3 * Real.log ℓ := by linarith
  have hk_lt : (k:ℝ) * (3 * Real.log ℓ) < ℓ := by rwa [lt_div_iff₀ h3log] at hkm
  have hk6 : 6 * (k:ℝ) < ℓ := by nlinarith
  have hkm1 : 0 < (k:ℝ) - 1 := by linarith
  have hu : 3 * Real.log ℓ < ℓ / ((k:ℝ) - 1) := by
    rw [lt_div_iff₀ hkm1]; nlinarith
  have hexpu : ℓ ^ 3 < Real.exp (ℓ / ((k:ℝ) - 1)) := by
    calc ℓ ^ 3 = Real.exp (3 * Real.log ℓ) := by
          rw [show (3:ℝ) * Real.log ℓ = ((3:ℕ):ℝ) * Real.log ℓ by norm_num, Real.exp_nat_mul,
            Real.exp_log hℓpos]
      _ < _ := Real.exp_lt_exp.mpr hu
  have hx0 : 0 ≤ ((k:ℝ) - 2) * ℓ := by nlinarith
  have hd_lt : (d:ℝ) < ((k:ℝ) - 2) * ℓ + 1 := by
    rw [hd, hkk]; exact Nat.ceil_lt_add_one hx0
  have hd_le : (d:ℝ) ≤ ((k:ℝ) - 1) * ℓ := by nlinarith
  set B := (n:ℝ) * Real.exp (-(((k:ℝ) - 2) * ℓ) / ((k:ℝ) - 1)) with hB
  have hBt : ∀ t : ℕ, t < d → B ≤ n * Real.exp (-(t:ℝ) / ((k:ℝ) - 1)) := by
    intro t ht
    have ht' : (t:ℝ) < ((k:ℝ) - 2) * ℓ := by
      have := Nat.lt_ceil.mp (hd ▸ ht)
      rwa [hkk] at this
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hkm1.le
    linarith
  have hBge : Real.exp (ℓ / ((k:ℝ) - 1)) / 2 ≤ B := by
    have : Real.exp (ℓ / ((k:ℝ) - 1)) =
        (m:ℝ) * Real.exp (-(((k:ℝ) - 2) * ℓ) / ((k:ℝ) - 1)) := by
      rw [show (m:ℝ) = Real.exp ℓ from (Real.exp_log hm_pos).symm, ← Real.exp_add]
      congr 1; field_simp; ring
    rw [this, hB]
    have := Real.exp_pos (-(((k:ℝ) - 2) * ℓ) / ((k:ℝ) - 1))
    nlinarith
  have hkm_nat : k ≤ m := by
    have h1 := Real.log_le_sub_one_of_pos hm_pos
    have : (k:ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hS_nat : (univ.filter (fun F : Finset (Fin L × Fin k) => F.card < d)).card ≤
      m ^ (3 * d) := by
    refine (aux_lc_subsets d).trans ?_
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have hmm : 2 * (L * k + 1) ≤ m ^ 3 := by
      have e1 : (2 * L) * k ≤ m * m := Nat.mul_le_mul (by omega) hkm_nat
      have e2 : 2 ≤ m := by omega
      have e3 : m * m + 2 ≤ m ^ 3 := by nlinarith
      nlinarith
    calc d * (L * k + 1) ^ d ≤ 2 ^ d * (L * k + 1) ^ d :=
          Nat.mul_le_mul_right _ (Nat.lt_two_pow_self).le
      _ = (2 * (L * k + 1)) ^ d := (mul_pow _ _ _).symm
      _ ≤ (m ^ 3) ^ d := Nat.pow_le_pow_left hmm _
      _ = m ^ (3 * d) := (pow_mul _ _ _).symm
  have hS_real : ((univ.filter (fun F : Finset (Fin L × Fin k) => F.card < d)).card : ℝ) *
      Real.exp (-B) < 1 := by
    have h1 : ((univ.filter (fun F : Finset (Fin L × Fin k) => F.card < d)).card : ℝ) ≤
        Real.exp (3 * d * ℓ) := by
      have : ((m ^ (3 * d) : ℕ) : ℝ) = Real.exp (3 * d * ℓ) := by
        rw [show (3 * (d:ℝ) * ℓ) = ((3 * d : ℕ) : ℝ) * ℓ by push_cast; ring, Real.exp_nat_mul,
          Real.exp_log hm_pos]
        push_cast; ring
      rw [← this]; exact_mod_cast hS_nat
    have h2 : 3 * d * ℓ < B := by
      have e1 : 3 * (d:ℝ) * ℓ ≤ 3 * (((k:ℝ) - 1) * ℓ) * ℓ := by
        have := mul_le_mul_of_nonneg_right hd_le hℓpos.le
        linarith
      have e2 : 3 * (((k:ℝ) - 1) * ℓ) * ℓ ≤ ℓ ^ 3 / 2 := by
        have h6 : 6 * ((k:ℝ) - 1) ≤ ℓ := by linarith
        have := mul_le_mul_of_nonneg_right h6 (sq_nonneg ℓ)
        nlinarith
      linarith
    calc _ ≤ Real.exp (3 * d * ℓ) * Real.exp (-B) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (3 * d * ℓ - B) := by rw [← Real.exp_add]; ring_nf
      _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  obtain ⟨g, hg⟩ := aux_lc_exists n L k d hk B hBt hS_real
  let zero : Fin k := ⟨0, by omega⟩
  let one : Fin k := ⟨1, by omega⟩
  refine ⟨{ part := fun b j => if h : b.val < n then g ⟨b.val, h⟩ j else
              if b.val = n + j.val + 1 then one else zero,
            distinct := ?_, cover_bound := ?_ }⟩
  · intro j j' hjj' hall
    have hb1 : n + j.val + 1 < m := by omega
    have hb0 : n < m := by omega
    have := hall ⟨n + j.val + 1, hb1⟩ ⟨n, hb0⟩
    have hjv : j.val ≠ j'.val := fun h => hjj' (Fin.ext h)
    have e1 : ¬ (n + j.val + 1 < n) := by omega
    have e2 : ¬ (n < n) := by omega
    have e3 : ¬ (n = n + j.val + 1) := by omega
    have e4 : ¬ (n + j.val + 1 = n + j'.val + 1) := by omega
    have e5 : ¬ (n = n + j'.val + 1) := by omega
    simp only [e1, e2, e3, e4, e5, dif_neg, not_false_eq_true, if_true, if_false, zero, one,
      Fin.mk.injEq, one_ne_zero, false_iff, not_true_eq_false] at this
  · intro F hF hcov
    by_contra hlt
    push Not at hlt
    obtain ⟨b, hb⟩ := hg F hF hlt
    obtain ⟨x, hx, hpx⟩ := hcov ⟨b.val, by omega⟩
    simp only [b.isLt, dif_pos] at hpx
    exact hb x hx hpx

end SetCoverThreshold.SetCover

open SetCoverThreshold.SetCover

theorem solution (c : ℝ) (hc : 0 ≤ c) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ L k : ℕ,
      (L : ℝ) ≤ (Real.logb 2 m) ^ c → 2 ≤ k →
        (k : ℝ) < Real.log m / (3 * Real.log (Real.log m)) →
          Nonempty (PartitionSystem m L k ⌈(1 - 2 / (k : ℝ)) * k * Real.log m⌉₊) := by
  obtain ⟨m₀, hm₀⟩ :=
    Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually (aux_lc_ev c))
  refine ⟨m₀, fun m hm L k hL hk hkm => ?_⟩
  obtain ⟨h1, h2⟩ := hm₀ m hm
  exact aux_lc_main m L k h1 (by linarith) hk hkm
