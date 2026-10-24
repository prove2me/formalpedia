-- Prove2me | solution 1 for SecretaryAdvice.Binary.proposition_12_binary
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T01:06:28.044431+00:00
-- url     : https://prove2.me/submissions/25a36acb-c11a-48c7-b5b2-32af00b9c907

import Mathlib
import Definitions.Def_SecretaryAdvice_Binary_Setting
import Definitions.Def_SecretaryAdvice_Binary_LP

set_option autoImplicit false


open SecretaryAdvice.Binary

namespace SA4


theorem greedy_stage (n : ℕ) (p p' : ℝ) : ∀ k : ℕ, k ≤ n → ∀ u : ℕ → Bool → ℝ,
    (∀ j, k < j → j ≤ n → ∀ s, u j s = max 0 (a n p s - chat j p' s *
      ∑ l ∈ Finset.Ioc j n, (u l true + u l false))) →
    (∀ j, k < j → ∀ s, (List.range k).reverse.foldl (greedyStep n p p') u j s = u j s) ∧
    (∀ j, 1 ≤ j → j ≤ n → ∀ s, (List.range k).reverse.foldl (greedyStep n p p') u j s =
      max 0 (a n p s - chat j p' s * ∑ l ∈ Finset.Ioc j n,
        ((List.range k).reverse.foldl (greedyStep n p p') u l true +
         (List.range k).reverse.foldl (greedyStep n p p') u l false))) := by
  intro k
  induction k with
  | zero =>
    intro _ u hu
    simp only [List.range_zero, List.reverse_nil, List.foldl_nil]
    exact ⟨by first | trivial | simp, fun j hj hjn s => hu j (by omega) hjn s⟩
  | succ k ih =>
    intro hk u hu
    have hlist : (List.range (k+1)).reverse = k :: (List.range k).reverse := by
      simp [List.range_succ]
    rw [hlist, List.foldl_cons]
    set u' := greedyStep n p p' u k with hu'
    have hu'eq : ∀ j s, u' j s = if j = k + 1 then max 0 (a n p s - chat (k+1) p' s *
        ∑ l ∈ Finset.Ioc (k+1) n, (u l true + u l false)) else u j s := by
      intro j s; rfl
    have hu'ne : ∀ j, j ≠ k + 1 → ∀ s, u' j s = u j s := by
      intro j hj s; rw [hu'eq]; simp [hj]
    have hsum : ∀ j, k + 1 ≤ j → ∑ l ∈ Finset.Ioc j n, (u' l true + u' l false) =
        ∑ l ∈ Finset.Ioc j n, (u l true + u l false) := by
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      have : l ≠ k + 1 := by have := (Finset.mem_Ioc.1 hl).1; omega
      rw [hu'ne l this, hu'ne l this]
    have hhyp : ∀ j, k < j → j ≤ n → ∀ s, u' j s = max 0 (a n p s - chat j p' s *
        ∑ l ∈ Finset.Ioc j n, (u' l true + u' l false)) := by
      intro j hj hjn s
      rw [hsum j (by omega)]
      by_cases h : j = k + 1
      · subst h; rw [hu'eq]; simp
      · rw [hu'ne j h]
        exact hu j (by omega) hjn s
    obtain ⟨ih1, ih2⟩ := ih (by omega) u' hhyp
    refine ⟨fun j hj s => ?_, ih2⟩
    rw [ih1 j (by omega), hu'ne j (by omega)]

theorem greedy_rec (n : ℕ) (p p' : ℝ) : ∀ i, 1 ≤ i → i ≤ n → ∀ s,
    greedy n p p' i s = max 0 (a n p s - chat i p' s *
      ∑ l ∈ Finset.Ioc i n, (greedy n p p' l true + greedy n p p' l false)) := by
  have := (greedy_stage n p p' n le_rfl (fun _ _ => 0) (fun j h1 h2 => by omega)).2
  intro i hi hin s
  exact this i hi hin s

theorem greedy_nonneg (n : ℕ) (p p' : ℝ) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Bool) :
    0 ≤ greedy n p p' i s := by
  rw [greedy_rec n p p' i hi hin s]; exact le_max_left _ _

noncomputable def Ufun (n : ℕ) (u : ℕ → Bool → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc i n, (u j true + u j false)

noncomputable def Cfun (p' : ℝ) (Z : ℕ → Bool → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 1 j, (chat i p' true * Z i true + chat i p' false * Z i false)

lemma swap_id (n : ℕ) (p' : ℝ) (Z u : ℕ → Bool → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, (chat i p' true * Z i true + chat i p' false * Z i false) * Ufun n u i =
    ∑ j ∈ Finset.Icc 1 n, (u j true + u j false) * Cfun p' Z j := by
  unfold Ufun Cfun
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 n) (s' := fun j => Finset.Ico 1 j)]
  · apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
  · intro i j
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_Ico]
    omega

lemma lp_identity (n : ℕ) (p p' : ℝ) (Z u : ℕ → Bool → ℝ) :
    primalValue n p Z = dualValue n u
      - ∑ i ∈ Finset.Icc 1 n, (Z i true * (u i true + chat i p' true * Ufun n u i - a n p true)
          + Z i false * (u i false + chat i p' false * Ufun n u i - a n p false))
      - ∑ i ∈ Finset.Icc 1 n, (u i true * (1 - Cfun p' Z i - Z i true)
          + u i false * (1 - Cfun p' Z i - Z i false)) := by
  have key := swap_id n p' Z u
  unfold primalValue dualValue
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have e : ∀ i ∈ Finset.Icc 1 n,
      (u i true + u i false
        - (Z i true * (u i true + chat i p' true * Ufun n u i - a n p true)
          + Z i false * (u i false + chat i p' false * Ufun n u i - a n p false))
        - (u i true * (1 - Cfun p' Z i - Z i true)
          + u i false * (1 - Cfun p' Z i - Z i false))) =
      (p * Z i true + (1 - p) * Z i false) / (n : ℝ)
        + (u i true + u i false) * Cfun p' Z i
        - (chat i p' true * Z i true + chat i p' false * Z i false) * Ufun n u i := by
    intro i _
    unfold a
    simp only [if_true, Bool.false_eq_true, if_false]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_add_distrib, key]
  ring

lemma chat_nonneg (i : ℕ) (p' : ℝ) (hp'0 : 0 ≤ p') (hp'1 : p' ≤ 1) (s : Bool) :
    0 ≤ chat i p' s := by
  unfold chat; cases s <;> simp <;> apply div_nonneg <;> first | positivity | linarith

lemma lp_le (n : ℕ) (p p' : ℝ) (Z u : ℕ → Bool → ℝ)
    (hZ : ∀ i, 1 ≤ i → i ≤ n → ∀ s, 0 ≤ Z i s ∧ Z i s ≤ 1 - Cfun p' Z i)
    (hu : DualFeasible n p p' u) :
    primalValue n p Z ≤ dualValue n u := by
  rw [lp_identity n p p' Z u]
  have h1 : 0 ≤ ∑ i ∈ Finset.Icc 1 n, (Z i true * (u i true + chat i p' true * Ufun n u i - a n p true)
          + Z i false * (u i false + chat i p' false * Ufun n u i - a n p false)) := by
    apply Finset.sum_nonneg; intro i hi
    rw [Finset.mem_Icc] at hi
    have := hZ i hi.1 hi.2 true; have := hZ i hi.1 hi.2 false
    have := hu i hi.1 hi.2 true; have := hu i hi.1 hi.2 false
    unfold Ufun
    apply add_nonneg <;> apply mul_nonneg <;> linarith
  have h2 : 0 ≤ ∑ i ∈ Finset.Icc 1 n, (u i true * (1 - Cfun p' Z i - Z i true)
          + u i false * (1 - Cfun p' Z i - Z i false)) := by
    apply Finset.sum_nonneg; intro i hi
    rw [Finset.mem_Icc] at hi
    have := hZ i hi.1 hi.2 true; have := hZ i hi.1 hi.2 false
    have := hu i hi.1 hi.2 true; have := hu i hi.1 hi.2 false
    apply add_nonneg <;> apply mul_nonneg <;> linarith
  linarith

lemma greedy_mono_le (n : ℕ) (p p' : ℝ)
    (hmono : ∀ i : ℕ, 1 ≤ i → i < n → ∀ s : Bool,
      greedy n p p' i s ≤ greedy n p p' (i + 1) s) (s : Bool) :
    ∀ i k, 1 ≤ i → i ≤ k → k ≤ n → greedy n p p' i s ≤ greedy n p p' k s := by
  intro i k hi hik hkn
  induction k, hik using Nat.le_induction with
  | base => exact le_refl _
  | succ k hk ih => exact le_trans (ih (by omega)) (hmono k (by omega) (by omega) s)

lemma thr_lp (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ)
    (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hmono : ∀ i : ℕ, 1 ≤ i → i < n → ∀ s : Bool,
      greedy n p p' i s ≤ greedy n p p' (i + 1) s) :
    ∃ tY tN : ℕ, 1 ≤ tY ∧ tY ≤ n ∧ 1 ≤ tN ∧ tN ≤ n ∧
      ∀ Z : ℕ → Bool → ℝ, (∀ k, 1 ≤ k → k ≤ n → ∀ s,
        Z k s = if (if s then tY else tN) ≤ k then 1 - Cfun p' Z k else 0) →
        primalValue n p Z = dualValue n (greedy n p p') := by
  classical
  have hsel : ∀ s : Bool, ∃ t, 1 ≤ t ∧ t ≤ n ∧
      (∀ k, 1 ≤ k → k < t → greedy n p p' k s = 0) ∧
      (∀ k, t ≤ k → k ≤ n → greedy n p p' k s =
        a n p s - chat k p' s * Ufun n (greedy n p p') k) := by
    intro s
    by_cases hex : ∃ i, 1 ≤ i ∧ i ≤ n ∧ 0 < greedy n p p' i s
    · refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1, ?_, ?_⟩
      · intro k hk1 hk2
        have hmin := Nat.find_min hex hk2
        have hkn : k ≤ n := le_trans hk2.le (Nat.find_spec hex).2.1
        have h0 := greedy_nonneg n p p' k hk1 hkn s
        by_contra hne
        exact hmin ⟨hk1, hkn, lt_of_le_of_ne h0 (Ne.symm hne)⟩
      · intro k hk1 hk2
        have hpos : 0 < greedy n p p' k s :=
          lt_of_lt_of_le (Nat.find_spec hex).2.2
            (greedy_mono_le n p p' hmono s _ _ (Nat.find_spec hex).1 hk1 hk2)
        have hr := greedy_rec n p p' k (le_trans (Nat.find_spec hex).1 hk1) hk2 s
        rw [hr] at hpos ⊢
        unfold Ufun
        rcases le_total (a n p s - chat k p' s *
          ∑ l ∈ Finset.Ioc k n, (greedy n p p' l true + greedy n p p' l false)) 0 with h | h
        · rw [max_eq_left h] at hpos; exact absurd hpos (lt_irrefl 0)
        · exact max_eq_right h
    · push Not at hex
      refine ⟨n, hn, le_rfl, ?_, ?_⟩
      · intro k hk1 hk2
        exact le_antisymm (hex k hk1 hk2.le) (greedy_nonneg n p p' k hk1 hk2.le s)
      · intro k hk1 hk2
        have hk : k = n := le_antisymm hk2 hk1
        rw [hk, greedy_rec n p p' n hn le_rfl s]
        unfold Ufun
        simp only [Finset.Ioc_self, Finset.sum_empty, mul_zero, sub_zero]
        apply max_eq_right
        unfold a; cases s <;> simp <;> apply div_nonneg <;> first | positivity | linarith
  obtain ⟨tY, hY1, hY2, hY3, hY4⟩ := hsel true
  obtain ⟨tN, hN1, hN2, hN3, hN4⟩ := hsel false
  refine ⟨tY, tN, hY1, hY2, hN1, hN2, ?_⟩
  intro Z hZ
  rw [lp_identity n p p' Z (greedy n p p')]
  have hcs : ∀ k, 1 ≤ k → k ≤ n → ∀ s,
      Z k s * (greedy n p p' k s + chat k p' s * Ufun n (greedy n p p') k - a n p s) = 0 ∧
      greedy n p p' k s * (1 - Cfun p' Z k - Z k s) = 0 := by
    intro k hk1 hk2 s
    have hz := hZ k hk1 hk2 s
    cases s
    · simp only [Bool.false_eq_true, if_false] at hz ⊢
      by_cases ht : tN ≤ k
      · rw [if_pos ht] at hz
        rw [hN4 k ht hk2, hz]; constructor <;> ring
      · rw [if_neg ht] at hz
        rw [hN3 k hk1 (by omega), hz]; constructor <;> ring
    · simp only [if_true] at hz ⊢
      by_cases ht : tY ≤ k
      · rw [if_pos ht] at hz
        rw [hY4 k ht hk2, hz]; constructor <;> ring
      · rw [if_neg ht] at hz
        rw [hY3 k hk1 (by omega), hz]; constructor <;> ring
  have h1 : ∑ i ∈ Finset.Icc 1 n, (Z i true * (greedy n p p' i true + chat i p' true *
      Ufun n (greedy n p p') i - a n p true) + Z i false * (greedy n p p' i false +
      chat i p' false * Ufun n (greedy n p p') i - a n p false)) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    rw [Finset.mem_Icc] at hi
    rw [(hcs i hi.1 hi.2 true).1, (hcs i hi.1 hi.2 false).1, add_zero]
  have h2 : ∑ i ∈ Finset.Icc 1 n, (greedy n p p' i true * (1 - Cfun p' Z i - Z i true) +
      greedy n p p' i false * (1 - Cfun p' Z i - Z i false)) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    rw [Finset.mem_Icc] at hi
    rw [(hcs i hi.1 hi.2 true).2, (hcs i hi.1 hi.2 false).2, add_zero]
  rw [h1, h2]; ring

end SA4


open Classical

namespace SA4

/-- relative-order pattern of the first `j+1` positions -/
def patt {m : ℕ} (j : ℕ) (π : Equiv.Perm (Fin m)) : Fin (j+1) → Fin (j+1) → Bool :=
  fun a b => if h : j < m then decide (π ⟨a.val, by omega⟩ ≤ π ⟨b.val, by omega⟩) else false

def Tpat {j : ℕ} (P : Fin (j+1) → Fin (j+1) → Bool) : Prop := ∀ a, P a (Fin.last j) = true

/-- insert value `v` at the last position -/
def insFun {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) : Fin (m+1) → Fin (m+1) :=
  Fin.lastCases v (fun k => v.succAbove (σ k))

@[simp] lemma insFun_last {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) :
    insFun v σ (Fin.last m) = v := by simp [insFun]

@[simp] lemma insFun_castSucc {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    insFun v σ (Fin.castSucc k) = v.succAbove (σ k) := by simp [insFun]

lemma insFun_inj {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) :
    Function.Injective (insFun v σ) := by
  intro x y hxy
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => rfl
    | cast k =>
      simp at hxy
  | cast k =>
    induction y using Fin.lastCases with
    | last =>
      simp at hxy
    | cast l =>
      simp at hxy
      rw [hxy]

noncomputable def ins {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m+1)) :=
  Equiv.ofBijective (insFun v σ) ((Finite.injective_iff_bijective).1 (insFun_inj v σ))

@[simp] lemma ins_apply {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) (x : Fin (m+1)) :
    ins v σ x = insFun v σ x := rfl

lemma ins_bij (m : ℕ) : Function.Bijective (fun x : Fin (m+1) × Equiv.Perm (Fin m) => ins x.1 x.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨v, σ⟩ ⟨v', σ'⟩ h
    simp only at h
    have hv : v = v' := by
      have := congrArg (fun π : Equiv.Perm (Fin (m+1)) => π (Fin.last m)) h
      simpa using this
    subst hv
    have hσ : σ = σ' := by
      ext k
      have := congrArg (fun π : Equiv.Perm (Fin (m+1)) => π (Fin.castSucc k)) h
      simp only [ins_apply, insFun_castSucc] at this
      rw [Fin.succAbove_right_inj] at this
      rw [this]
    rw [hσ]
  · simp [Fintype.card_perm, Nat.factorial_succ]

lemma sum_perm_succ {m : ℕ} (F : Equiv.Perm (Fin (m+1)) → ℝ) :
    ∑ π, F π = ∑ v : Fin (m+1), ∑ σ : Equiv.Perm (Fin m), F (ins v σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (ins_bij m) _ _ (fun x => rfl)).symm

lemma patt_ins {m : ℕ} (j : ℕ) (hj : j < m) (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) :
    patt j (ins v σ) = patt j σ := by
  funext a b
  unfold patt
  rw [dif_pos (by omega), dif_pos hj]
  have ha : (⟨a.val, by omega⟩ : Fin (m+1)) = Fin.castSucc ⟨a.val, by omega⟩ := rfl
  have hb : (⟨b.val, by omega⟩ : Fin (m+1)) = Fin.castSucc ⟨b.val, by omega⟩ := rfl
  rw [ha, hb, ins_apply, ins_apply, insFun_castSucc, insFun_castSucc]
  simp only [Fin.succAbove_le_succAbove_iff]

lemma top_succAbove {m : ℕ} (v : Fin (m+1)) (y : Fin m) :
    (v.succAbove y).val + 1 = m + 1 ↔ (v.val ≠ m ∧ y.val + 1 = m) := by
  rcases lt_or_ge (Fin.castSucc y) v with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have : y.val < v.val := h
    simp only [Fin.val_castSucc]
    constructor
    · intro h1; omega
    · intro h1; have := v.isLt; omega
  · rw [Fin.succAbove_of_le_castSucc _ _ h]
    have : v.val ≤ y.val := h
    simp only [Fin.val_succ]
    constructor
    · intro h1; omega
    · intro h1; omega

lemma ins_top_cast {m : ℕ} (v : Fin (m+1)) (σ : Equiv.Perm (Fin m)) (i : ℕ) (hi : i < m) :
    ((ins v σ) ⟨i, by omega⟩).val + 1 = m + 1 ↔ (v.val ≠ m ∧ (σ ⟨i, hi⟩).val + 1 = m) := by
  have : (⟨i, by omega⟩ : Fin (m+1)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this, ins_apply, insFun_castSucc, top_succAbove]

lemma sum_ne_last {m : ℕ} (c : ℝ) :
    ∑ v : Fin (m+1), (if v.val ≠ m then c else 0) = m * c := by
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_congr rfl (fun x _ => if_pos (show (Fin.castSucc x).val ≠ m from by
    simp only [Fin.val_castSucc]; omega))]
  simp

lemma Tpat_base (j : ℕ) (π : Equiv.Perm (Fin (j+1))) :
    Tpat (patt j π) ↔ (π ⟨j, by omega⟩).val + 1 = j + 1 := by
  unfold Tpat patt
  simp only [dif_pos (show j < j + 1 by omega), decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := π.surjective (Fin.last j)
    have := h ⟨a.val, a.isLt⟩
    simp only [Fin.val_last] at this
    have e : (⟨a.val, a.isLt⟩ : Fin (j+1)) = a := rfl
    rw [e, ha] at this
    have h2 : (Fin.last j).val ≤ (π ⟨j, by omega⟩).val := this
    have h3 := (π ⟨j, by omega⟩).isLt
    simp at h2; omega
  · intro h a
    show (π ⟨a.val, _⟩).val ≤ (π ⟨(Fin.last j).val, _⟩).val
    simp only [Fin.val_last]
    have := (π ⟨a.val, by omega⟩).isLt
    omega

/-- Lemma (C) -/
lemma lemC (j : ℕ) (H : (Fin (j+1) → Fin (j+1) → Bool) → ℝ) :
    ∀ m (hm : j < m), ((j:ℝ)+1) * ∑ π : Equiv.Perm (Fin m),
        (if Tpat (patt j π) then H (patt j π) else 0) =
      (m:ℝ) * ∑ π : Equiv.Perm (Fin m),
        (if (π ⟨j, hm⟩).val + 1 = m then H (patt j π) else 0) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    congr 1
    · push_cast; ring
    apply Finset.sum_congr rfl
    intro π _
    by_cases h : Tpat (patt j π)
    · rw [if_pos h, if_pos]; exact (Tpat_base j π).1 h
    · rw [if_neg h, if_neg]; exact (fun h' => h ((Tpat_base j π).2 h'))
  | succ m hm ih =>
    rw [sum_perm_succ, sum_perm_succ]
    have e1 : ∀ v : Fin (m+1), ∑ σ : Equiv.Perm (Fin m),
        (if Tpat (patt j (ins v σ)) then H (patt j (ins v σ)) else 0) =
        ∑ σ : Equiv.Perm (Fin m), (if Tpat (patt j σ) then H (patt j σ) else 0) := by
      intro v; apply Finset.sum_congr rfl; intro σ _; rw [patt_ins j hm]
    have e2 : ∀ v : Fin (m+1), ∑ σ : Equiv.Perm (Fin m),
        (if ((ins v σ) ⟨j, by omega⟩).val + 1 = m + 1 then H (patt j (ins v σ)) else 0) =
        (if v.val ≠ m then ∑ σ : Equiv.Perm (Fin m),
          (if (σ ⟨j, hm⟩).val + 1 = m then H (patt j σ) else 0) else 0) := by
      intro v
      by_cases hv : v.val ≠ m
      · rw [if_pos hv]
        apply Finset.sum_congr rfl; intro σ _
        rw [patt_ins j hm]
        by_cases h2 : (σ ⟨j, hm⟩).val + 1 = m
        · rw [if_pos h2, if_pos ((ins_top_cast v σ j hm).2 ⟨hv, h2⟩)]
        · rw [if_neg h2, if_neg (fun h' => h2 ((ins_top_cast v σ j hm).1 h').2)]
      · rw [if_neg hv]
        apply Finset.sum_eq_zero; intro σ _
        rw [if_neg (fun h' => hv ((ins_top_cast v σ j hm).1 h').1)]
    simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [sum_ne_last]
    push_cast
    rw [← ih]
    ring

/-- count of permutations with top at position i -/
lemma count_top : ∀ m (i : ℕ) (hi : i < m),
    ∑ π : Equiv.Perm (Fin m), (if (π ⟨i, hi⟩).val + 1 = m then (1:ℝ) else 0) =
      ((m - 1).factorial : ℝ) := by
  intro m i hi
  induction m, hi using Nat.le_induction with
  | base =>
    rw [sum_perm_succ]
    have : ∀ v : Fin (i+1), ∑ σ : Equiv.Perm (Fin i),
        (if ((ins v σ) ⟨i, by omega⟩).val + 1 = i + 1 then (1:ℝ) else 0) =
        if v.val = i then (i.factorial : ℝ) else 0 := by
      intro v
      have e : (⟨i, by omega⟩ : Fin (i+1)) = Fin.last i := rfl
      simp only [e, ins_apply, insFun_last]
      by_cases hv : v.val = i
      · rw [if_pos hv]; simp [hv, Fintype.card_perm]
      · rw [if_neg hv]; simp [hv]
    simp only [this]
    rw [Fin.sum_univ_castSucc]
    rw [Finset.sum_eq_zero (fun x _ => if_neg (show (Fin.castSucc x).val ≠ i from by
      simp only [Fin.val_castSucc]; omega))]
    simp
  | succ m hm ih =>
    rw [sum_perm_succ]
    have : ∀ v : Fin (m+1), ∑ σ : Equiv.Perm (Fin m),
        (if ((ins v σ) ⟨i, by omega⟩).val + 1 = m + 1 then (1:ℝ) else 0) =
        if v.val ≠ m then ((m-1).factorial : ℝ) else 0 := by
      intro v
      rw [← ih]
      by_cases hv : v.val ≠ m
      · rw [if_pos hv]
        apply Finset.sum_congr rfl; intro σ _
        by_cases h2 : (σ ⟨i, hm⟩).val + 1 = m
        · rw [if_pos h2, if_pos ((ins_top_cast v σ i hm).2 ⟨hv, h2⟩)]
        · rw [if_neg h2, if_neg (fun h' => h2 ((ins_top_cast v σ i hm).1 h').2)]
      · rw [if_neg hv]
        apply Finset.sum_eq_zero; intro σ _
        rw [if_neg (fun h' => hv ((ins_top_cast v σ i hm).1 h').1)]
    simp only [this]
    rw [sum_ne_last]
    have : m = (m - 1) + 1 := by omega
    simp only [Nat.add_sub_cancel]
    rw [this, Nat.factorial_succ]
    push_cast
    simp

/-- Lemma (A') -/
lemma lemA' (j i : ℕ) (hji : j < i) (H : (Fin (j+1) → Fin (j+1) → Bool) → ℝ) :
    ∀ m (hm : i < m), ((j:ℝ)+1) * ∑ π : Equiv.Perm (Fin m),
        (if (π ⟨i, hm⟩).val + 1 = m then (if Tpat (patt j π) then H (patt j π) else 0) else 0) =
      ∑ π : Equiv.Perm (Fin m),
        (if (π ⟨j, by omega⟩).val + 1 = m then H (patt j π) else 0) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    rw [sum_perm_succ, sum_perm_succ]
    have e1 : ∀ v : Fin (i+1), ∑ σ : Equiv.Perm (Fin i),
        (if ((ins v σ) ⟨i, by omega⟩).val + 1 = i + 1 then
          (if Tpat (patt j (ins v σ)) then H (patt j (ins v σ)) else 0) else 0) =
        if v.val = i then ∑ σ : Equiv.Perm (Fin i),
          (if Tpat (patt j σ) then H (patt j σ) else 0) else 0 := by
      intro v
      have e : (⟨i, by omega⟩ : Fin (i+1)) = Fin.last i := rfl
      simp only [e, ins_apply, insFun_last, patt_ins j hji]
      by_cases hv : v.val = i
      · rw [if_pos hv]; apply Finset.sum_congr rfl; intro σ _; rw [if_pos (by omega)]
      · rw [if_neg hv]; apply Finset.sum_eq_zero; intro σ _; rw [if_neg (by omega)]
    have e2 : ∀ v : Fin (i+1), ∑ σ : Equiv.Perm (Fin i),
        (if ((ins v σ) ⟨j, by omega⟩).val + 1 = i + 1 then H (patt j (ins v σ)) else 0) =
        (if v.val ≠ i then ∑ σ : Equiv.Perm (Fin i),
          (if (σ ⟨j, hji⟩).val + 1 = i then H (patt j σ) else 0) else 0) := by
      intro v
      by_cases hv : v.val ≠ i
      · rw [if_pos hv]
        apply Finset.sum_congr rfl; intro σ _
        rw [patt_ins j hji]
        by_cases h2 : (σ ⟨j, hji⟩).val + 1 = i
        · rw [if_pos h2, if_pos ((ins_top_cast v σ j hji).2 ⟨hv, h2⟩)]
        · rw [if_neg h2, if_neg (fun h' => h2 ((ins_top_cast v σ j hji).1 h').2)]
      · rw [if_neg hv]
        apply Finset.sum_eq_zero; intro σ _
        rw [if_neg (fun h' => hv ((ins_top_cast v σ j hji).1 h').1)]
    simp only [e1, e2]
    rw [sum_ne_last, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, if_true]
    have hz : ∀ x : Fin i, (if x.val = i then ∑ σ : Equiv.Perm (Fin i),
          (if Tpat (patt j σ) then H (patt j σ) else 0) else (0:ℝ)) = 0 := by
      intro x; rw [if_neg (by omega)]
    simp only [hz, Finset.sum_const_zero, zero_add]
    exact lemC j H i hji
  | succ m hm ih =>
    rw [sum_perm_succ, sum_perm_succ]
    have e1 : ∀ v : Fin (m+1), ∑ σ : Equiv.Perm (Fin m),
        (if ((ins v σ) ⟨i, by omega⟩).val + 1 = m + 1 then
          (if Tpat (patt j (ins v σ)) then H (patt j (ins v σ)) else 0) else 0) =
        if v.val ≠ m then ∑ σ : Equiv.Perm (Fin m),
          (if (σ ⟨i, hm⟩).val + 1 = m then
            (if Tpat (patt j σ) then H (patt j σ) else 0) else 0) else 0 := by
      intro v
      by_cases hv : v.val ≠ m
      · rw [if_pos hv]
        apply Finset.sum_congr rfl; intro σ _
        rw [patt_ins j (by omega)]
        by_cases h2 : (σ ⟨i, hm⟩).val + 1 = m
        · rw [if_pos h2, if_pos ((ins_top_cast v σ i hm).2 ⟨hv, h2⟩)]
        · rw [if_neg h2, if_neg (fun h' => h2 ((ins_top_cast v σ i hm).1 h').2)]
      · rw [if_neg hv]
        apply Finset.sum_eq_zero; intro σ _
        rw [if_neg (fun h' => hv ((ins_top_cast v σ i hm).1 h').1)]
    have e2 : ∀ v : Fin (m+1), ∑ σ : Equiv.Perm (Fin m),
        (if ((ins v σ) ⟨j, by omega⟩).val + 1 = m + 1 then H (patt j (ins v σ)) else 0) =
        (if v.val ≠ m then ∑ σ : Equiv.Perm (Fin m),
          (if (σ ⟨j, by omega⟩).val + 1 = m then H (patt j σ) else 0) else 0) := by
      intro v
      have hjm : j < m := by omega
      by_cases hv : v.val ≠ m
      · rw [if_pos hv]
        apply Finset.sum_congr rfl; intro σ _
        rw [patt_ins j hjm]
        by_cases h2 : (σ ⟨j, hjm⟩).val + 1 = m
        · rw [if_pos h2, if_pos ((ins_top_cast v σ j hjm).2 ⟨hv, h2⟩)]
        · rw [if_neg h2, if_neg (fun h' => h2 ((ins_top_cast v σ j hjm).1 h').2)]
      · rw [if_neg hv]
        apply Finset.sum_eq_zero; intro σ _
        rw [if_neg (fun h' => hv ((ins_top_cast v σ j hjm).1 h').1)]
    simp only [e1, e2]
    rw [sum_ne_last, sum_ne_last, ← ih]
    ring

end SA4


open Classical
open SecretaryAdvice.Binary

namespace SA4

noncomputable def Nl (p' : ℝ) (b : Bool) : ℝ := if b then 1 - p' else p'
noncomputable def Tl (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

noncomputable def mu (n : ℕ) (p' : ℝ) (sig : Fin n → Bool) : ℝ := ∏ k, Nl p' (sig k)

noncomputable def nu (n : ℕ) (p' : ℝ) (i : Fin n) (s : Bool) (sig : Fin n → Bool) : ℝ :=
  if sig i = s then ∏ k ∈ Finset.univ.erase i, Nl p' (sig k) else 0

lemma Nl_nonneg (p' : ℝ) (h0 : 0 ≤ p') (h1 : p' ≤ 1) (b : Bool) : 0 ≤ Nl p' b := by
  unfold Nl; cases b <;> simp <;> linarith

lemma Nl_sum (p' : ℝ) (b : Bool) : Nl p' b + Nl p' (!b) = 1 := by
  unfold Nl; cases b <;> simp

lemma nu_nonneg (n : ℕ) (p' : ℝ) (h0 : 0 ≤ p') (h1 : p' ≤ 1) (i : Fin n) (s : Bool)
    (sig : Fin n → Bool) : 0 ≤ nu n p' i s sig := by
  unfold nu; split_ifs
  · exact Finset.prod_nonneg (fun k _ => Nl_nonneg p' h0 h1 _)
  · exact le_refl _

lemma mu_sum (n : ℕ) (p' : ℝ) : ∑ sig : Fin n → Bool, mu n p' sig = 1 := by
  unfold mu
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => Nl p' b)]
  apply Finset.prod_eq_one
  intro k _
  rw [Fintype.sum_bool]; unfold Nl; simp

lemma mu_split (n : ℕ) (p' : ℝ) (i : Fin n) (sig : Fin n → Bool) :
    mu n p' sig = Nl p' (sig i) * ∏ k ∈ Finset.univ.erase i, Nl p' (sig k) := by
  unfold mu
  exact (Finset.mul_prod_erase _ (fun k => Nl p' (sig k)) (Finset.mem_univ i)).symm

/-- flip the signal at `i` -/
def flipAt {n : ℕ} (i : Fin n) (sig : Fin n → Bool) : Fin n → Bool :=
  Function.update sig i (!sig i)

lemma flipAt_invol {n : ℕ} (i : Fin n) : Function.Involutive (flipAt i) := by
  intro sig
  unfold flipAt
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [Function.update_of_ne hk]

lemma S2 (n : ℕ) (p' : ℝ) (i : Fin n) (s : Bool) (G : (Fin n → Bool) → ℝ)
    (hG : ∀ sig b, G (Function.update sig i b) = G sig) :
    ∑ sig, nu n p' i s sig * G sig = ∑ sig, mu n p' sig * G sig := by
  set R : (Fin n → Bool) → ℝ := fun sig => ∏ k ∈ Finset.univ.erase i, Nl p' (sig k) with hR
  have hRflip : ∀ sig, R (flipAt i sig) = R sig := by
    intro sig
    simp only [hR]
    apply Finset.prod_congr rfl
    intro k hk
    have : k ≠ i := Finset.ne_of_mem_erase hk
    simp [flipAt, Function.update_of_ne this]
  have hGflip : ∀ sig, G (flipAt i sig) = G sig := fun sig => hG sig _
  have hflipi : ∀ sig, (flipAt i sig) i = !sig i := by intro sig; simp [flipAt]
  have hX : ∑ sig, (if sig i = !s then R sig * G sig else 0) =
      ∑ sig, (if sig i = s then R sig * G sig else 0) := by
    let e : Equiv.Perm (Fin n → Bool) := (flipAt_invol i).toPerm
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro sig _
    show (if (flipAt i sig) i = !s then R (flipAt i sig) * G (flipAt i sig) else 0) = _
    rw [hflipi, hRflip, hGflip]
    cases s <;> cases sig i <;> simp
  have hmu : ∀ sig, mu n p' sig * G sig =
      Nl p' s * (if sig i = s then R sig * G sig else 0) +
      Nl p' (!s) * (if sig i = !s then R sig * G sig else 0) := by
    intro sig
    rw [mu_split n p' i sig]
    cases s <;> cases h : sig i <;> simp [h, hR] <;> ring
  rw [Finset.sum_congr rfl (fun sig _ => hmu sig), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hX, ← add_mul, Nl_sum, one_mul]
  apply Finset.sum_congr rfl
  intro sig _
  unfold nu
  split_ifs <;> simp [hR]

lemma S3 (n : ℕ) (p' : ℝ) (j : Fin n) (sig : Fin n → Bool) :
    ∑ s' : Bool, Nl p' s' * nu n p' j s' sig = mu n p' sig := by
  rw [Fintype.sum_bool, mu_split n p' j sig]
  unfold nu
  cases h : sig j <;> simp

/-- weights of the conditional expectation given that the top secretary is at `i` with signal `s` -/
noncomputable def ezw (n : ℕ) (p' : ℝ) (i : Fin n) (s : Bool) (ω : Outcome n) : ℝ :=
  if (ω.1 i).val + 1 = n then nu n p' i s ω.2 else 0

noncomputable def Ez (n : ℕ) (p' : ℝ) (i : Fin n) (s : Bool) (H : Outcome n → ℝ) : ℝ :=
  (1 / ((n - 1).factorial : ℝ)) * ∑ ω : Outcome n, ezw n p' i s ω * H ω

lemma ezw_nonneg (n : ℕ) (p' : ℝ) (h0 : 0 ≤ p') (h1 : p' ≤ 1) (i : Fin n) (s : Bool)
    (ω : Outcome n) : 0 ≤ ezw n p' i s ω := by
  unfold ezw; split_ifs
  · exact nu_nonneg n p' h0 h1 i s ω.2
  · exact le_refl _

lemma Ez_mono (n : ℕ) (p' : ℝ) (h0 : 0 ≤ p') (h1 : p' ≤ 1) (i : Fin n) (s : Bool)
    (H H' : Outcome n → ℝ) (h : ∀ ω, H ω ≤ H' ω) : Ez n p' i s H ≤ Ez n p' i s H' := by
  unfold Ez
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (h ω) (ezw_nonneg n p' h0 h1 i s ω)

lemma Ez_nonneg (n : ℕ) (p' : ℝ) (h0 : 0 ≤ p') (h1 : p' ≤ 1) (i : Fin n) (s : Bool)
    (H : Outcome n → ℝ) (h : ∀ ω, 0 ≤ H ω) : 0 ≤ Ez n p' i s H := by
  unfold Ez
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (ezw_nonneg n p' h0 h1 i s ω) (h ω)

lemma Ez_sub (n : ℕ) (p' : ℝ) (i : Fin n) (s : Bool) (H H' : Outcome n → ℝ) :
    Ez n p' i s (fun ω => H ω - H' ω) = Ez n p' i s H - Ez n p' i s H' := by
  unfold Ez
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1; apply Finset.sum_congr rfl; intro ω _; ring

lemma Ez_sum {ι : Type} (S : Finset ι) (n : ℕ) (p' : ℝ) (i : Fin n) (s : Bool)
    (H : ι → Outcome n → ℝ) :
    Ez n p' i s (fun ω => ∑ j ∈ S, H j ω) = ∑ j ∈ S, Ez n p' i s (H j) := by
  unfold Ez
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma Ez_const_mul (n : ℕ) (p' : ℝ) (i : Fin n) (s : Bool) (c : ℝ) (H : Outcome n → ℝ) :
    Ez n p' i s (fun ω => c * H ω) = c * Ez n p' i s H := by
  unfold Ez
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro ω _; ring

lemma Ez_congr (n : ℕ) (p' : ℝ) (i : Fin n) (s : Bool) (H H' : Outcome n → ℝ)
    (h : ∀ ω : Outcome n, (ω.1 i).val + 1 = n → ω.2 i = s → H ω = H' ω) :
    Ez n p' i s H = Ez n p' i s H' := by
  unfold Ez
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  unfold ezw nu
  by_cases h1 : (ω.1 i).val + 1 = n
  · by_cases h2 : ω.2 i = s
    · rw [h ω h1 h2]
    · simp [h1, h2]
  · simp [h1]

lemma Ez_one (n : ℕ) (p' : ℝ) (i : Fin n) (s : Bool) :
    Ez n p' i s (fun _ => 1) = 1 := by
  unfold Ez ezw
  rw [Fintype.sum_prod_type]
  have : ∀ π : Equiv.Perm (Fin n), ∑ sig : Fin n → Bool,
      (if (π i).val + 1 = n then nu n p' i s sig else 0) * 1 =
      if (π i).val + 1 = n then (1:ℝ) else 0 := by
    intro π
    by_cases h : (π i).val + 1 = n
    · simp only [if_pos h, mul_one]
      have := S2 n p' i s (fun _ => 1) (fun _ _ => rfl)
      simp only [mul_one] at this
      rw [this, mu_sum]
    · simp [h]
  simp only [this]
  have hc := count_top n i.val i.isLt
  rw [hc]
  have : ((n - 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- info j depends only on the pattern and the signal prefix -/
lemma info_fst {n : ℕ} (j : Fin n) (ω : Outcome n) : (info j ω).1 = patt j.val ω.1 := by
  funext a b
  show decide (ω.1 ⟨a.val, by omega⟩ ≤ ω.1 ⟨b.val, by omega⟩) = _
  unfold patt
  rw [dif_pos j.isLt]

lemma info_eq {n : ℕ} (j : Fin n) (π : Equiv.Perm (Fin n)) (sig : Fin n → Bool) :
    info j (π, sig) = (patt j.val π, fun a => sig ⟨a.val, by omega⟩) := by
  rw [Prod.ext_iff]
  exact ⟨info_fst j (π, sig), rfl⟩

lemma bestSoFar_iff {n : ℕ} (j : Fin n) (ω : Outcome n) :
    bestSoFar j (info j ω) ↔ Tpat (patt j.val ω.1) := by
  unfold bestSoFar Tpat
  rw [info_fst]

lemma info_update {n : ℕ} (i j : Fin n) (hji : j < i) (π : Equiv.Perm (Fin n))
    (sig : Fin n → Bool) (b : Bool) :
    info j (π, Function.update sig i b) = info j (π, sig) := by
  rw [info_eq, info_eq]
  congr 1
  funext a
  have : (⟨a.val, by omega⟩ : Fin n) ≠ i := by
    intro h
    have := congrArg Fin.val h
    simp at this
    have := a.isLt
    have : j.val < i.val := hji
    omega
  simp [Function.update_of_ne this]

/-- Lemma (A): conditioning identity. -/
lemma lemA (n : ℕ) (p' : ℝ) (i j : Fin n) (hji : j < i) (s : Bool)
    (F : Info n j → ℝ) :
    Ez n p' i s (fun ω => if bestSoFar j (info j ω) then F (info j ω) else 0) =
      ∑ s' : Bool, chat (j.val + 1) p' s' * Ez n p' j s' (fun ω => F (info j ω)) := by
  have hjv : j.val < i.val := hji
  -- LHS
  have hL : Ez n p' i s (fun ω => if bestSoFar j (info j ω) then F (info j ω) else 0) =
      (1 / ((n - 1).factorial : ℝ)) * ∑ sig : Fin n → Bool, mu n p' sig *
        ∑ π : Equiv.Perm (Fin n), (if (π i).val + 1 = n then
          (if Tpat (patt j.val π) then F (info j (π, sig)) else 0) else 0) := by
    unfold Ez ezw
    congr 1
    rw [Fintype.sum_prod_type]
    have e1 : ∀ π : Equiv.Perm (Fin n), ∑ sig : Fin n → Bool,
        (if (π i).val + 1 = n then nu n p' i s sig else 0) *
          (if bestSoFar j (info j (π, sig)) then F (info j (π, sig)) else 0) =
        ∑ sig : Fin n → Bool, mu n p' sig * (if (π i).val + 1 = n then
          (if Tpat (patt j.val π) then F (info j (π, sig)) else 0) else 0) := by
      intro π
      by_cases h : (π i).val + 1 = n
      · simp only [if_pos h]
        have hb : ∀ sig : Fin n → Bool, bestSoFar j (info j (π, sig)) ↔ Tpat (patt j.val π) :=
          fun sig => bestSoFar_iff j (π, sig)
        simp only [hb]
        apply S2 n p' i s
        intro sig b
        simp only [info_update i j hji]
      · simp [h]
    rw [Finset.sum_congr rfl (fun π _ => e1 π), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro sig _
    rw [Finset.mul_sum]
  -- RHS
  have hR : ∑ s' : Bool, chat (j.val + 1) p' s' * Ez n p' j s' (fun ω => F (info j ω)) =
      (1 / ((j.val : ℝ) + 1)) * ((1 / ((n - 1).factorial : ℝ)) *
        ∑ sig : Fin n → Bool, mu n p' sig *
        ∑ π : Equiv.Perm (Fin n), (if (π j).val + 1 = n then F (info j (π, sig)) else 0)) := by
    unfold Ez ezw chat
    have hc : ∀ s' : Bool, (if s' = true then 1 - p' else p') / ((j.val + 1 : ℕ) : ℝ) =
        (1 / ((j.val : ℝ) + 1)) * Nl p' s' := by
      intro s'; unfold Nl; push_cast; cases s' <;> simp <;> ring
    simp only [hc]
    have e2 : ∀ s' : Bool, (1 / ((j.val : ℝ) + 1)) * Nl p' s' *
        ((1 / ((n - 1).factorial : ℝ)) * ∑ ω : Outcome n,
          (if (ω.1 j).val + 1 = n then nu n p' j s' ω.2 else 0) * F (info j ω)) =
        (1 / ((j.val : ℝ) + 1)) * ((1 / ((n - 1).factorial : ℝ)) *
          ∑ sig : Fin n → Bool, Nl p' s' * nu n p' j s' sig *
          ∑ π : Equiv.Perm (Fin n), (if (π j).val + 1 = n then F (info j (π, sig)) else 0)) := by
      intro s'
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro sig _
      apply Finset.sum_congr rfl; intro π _
      split_ifs <;> ring
    simp only [e2]
    rw [Fintype.sum_bool, ← mul_add, ← mul_add, ← Finset.sum_add_distrib]
    congr 2
    apply Finset.sum_congr rfl; intro sig _
    rw [← add_mul, ← S3 n p' j sig, Fintype.sum_bool]
  rw [hL, hR]
  -- per-signal identity from lemA'
  have key : ∀ sig : Fin n → Bool, ((j.val : ℝ) + 1) * ∑ π : Equiv.Perm (Fin n),
      (if (π i).val + 1 = n then
        (if Tpat (patt j.val π) then F (info j (π, sig)) else 0) else 0) =
      ∑ π : Equiv.Perm (Fin n), (if (π j).val + 1 = n then F (info j (π, sig)) else 0) := by
    intro sig
    have h := lemA' j.val i.val hjv (fun P => F (P, fun a => sig ⟨a.val, by omega⟩)) n i.isLt
    simp only [info_eq]
    exact h
  have hj1 : ((j.val : ℝ) + 1) ≠ 0 := by positivity
  have hs : ∀ sig : Fin n → Bool, mu n p' sig * ∑ π : Equiv.Perm (Fin n),
      (if (π i).val + 1 = n then
        (if Tpat (patt j.val π) then F (info j (π, sig)) else 0) else 0) =
      (1 / ((j.val : ℝ) + 1)) * (mu n p' sig * ∑ π : Equiv.Perm (Fin n),
        (if (π j).val + 1 = n then F (info j (π, sig)) else 0)) := by
    intro sig
    rw [← key sig]
    field_simp
  rw [Finset.sum_congr rfl (fun sig _ => hs sig), ← Finset.mul_sum]
  ring

end SA4


open Classical
open SecretaryAdvice.Binary

namespace SA4

/-- the predecessors of round `i` -/
noncomputable def filt {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => j.val < i.val)

lemma mem_filt {n : ℕ} (i j : Fin n) : j ∈ filt i ↔ j.val < i.val := by
  simp [filt]

lemma filt_sum {n : ℕ} (i : Fin n) (f : ℕ → ℝ) :
    ∑ j ∈ filt i, f j.val = ∑ k ∈ Finset.range i.val, f k := by
  unfold filt
  rw [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < i.val then f k else 0) n]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  have := i.isLt
  omega

lemma filt_prod {n : ℕ} (i : Fin n) (f : ℕ → ℝ) :
    ∏ j ∈ filt i, f j.val = ∏ k ∈ Finset.range i.val, f k := by
  unfold filt
  rw [Finset.prod_filter]
  rw [Fin.prod_univ_eq_prod_range (fun k => if k < i.val then f k else 1) n]
  rw [← Finset.prod_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  have := i.isLt
  omega

lemma tele_nat (b : ℕ → ℝ) : ∀ m : ℕ,
    ∑ k ∈ Finset.range m, b k * ∏ l ∈ Finset.range k, (1 - b l) =
      1 - ∏ l ∈ Finset.range m, (1 - b l) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, Finset.prod_range_succ, ih]; ring

lemma tele {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ filt i, a j * ∏ k ∈ filt j, (1 - a k) = 1 - ∏ k ∈ filt i, (1 - a k) := by
  set b : ℕ → ℝ := fun k => if h : k < n then a ⟨k, h⟩ else 0 with hb
  have hab : ∀ k : Fin n, a k = b k.val := by intro k; simp [hb, k.isLt]
  have h1 : ∀ j : Fin n, ∏ k ∈ filt j, (1 - a k) = ∏ l ∈ Finset.range j.val, (1 - b l) := by
    intro j
    rw [← filt_prod j (fun l => 1 - b l)]
    apply Finset.prod_congr rfl; intro k _; rw [hab]
  have h2 : ∑ j ∈ filt i, a j * ∏ k ∈ filt j, (1 - a k) =
      ∑ j ∈ filt i, (fun m => b m * ∏ l ∈ Finset.range m, (1 - b l)) j.val := by
    apply Finset.sum_congr rfl; intro j _; rw [h1, hab]
  rw [h2, filt_sum i (fun m => b m * ∏ l ∈ Finset.range m, (1 - b l)), h1 i, tele_nat]

/-- the probability of stopping exactly at round `i` -/
noncomputable def sg {n : ℕ} (q : Policy n) (i : Fin n) (ω : Outcome n) : ℝ :=
  q i (info i ω) * ∏ j ∈ filt i, (1 - q j (info j ω))

lemma sg_nonneg {n : ℕ} (q : Policy n) (hq : ValidPolicy q) (i : Fin n) (ω : Outcome n) :
    0 ≤ sg q i ω := by
  unfold sg
  apply mul_nonneg (hq i _).1
  apply Finset.prod_nonneg
  intro j _; have := (hq j (info j ω)).2; linarith

lemma sg_tele {n : ℕ} (q : Policy n) (i : Fin n) (ω : Outcome n) :
    ∏ j ∈ filt i, (1 - q j (info j ω)) = 1 - ∑ j ∈ filt i, sg q j ω := by
  have := tele (fun k => q k (info k ω)) i
  unfold sg
  linarith

lemma sg_le {n : ℕ} (q : Policy n) (hq : ValidPolicy q) (i : Fin n) (ω : Outcome n) :
    sg q i ω ≤ 1 - ∑ j ∈ filt i, sg q j ω := by
  rw [← sg_tele]
  unfold sg
  have hP : 0 ≤ ∏ j ∈ filt i, (1 - q j (info j ω)) := by
    apply Finset.prod_nonneg
    intro j _; have := (hq j (info j ω)).2; linarith
  have := (hq i (info i ω)).2
  nlinarith

/-- restriction of information -/
def restr {n : ℕ} (k j : Fin n) (x : Info n j) : Info n k :=
  (fun a b => if h : k.val ≤ j.val then x.1 ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ else false,
   fun a => if h : k.val ≤ j.val then x.2 ⟨a.val, by omega⟩ else false)

lemma restr_info {n : ℕ} (k j : Fin n) (h : k.val ≤ j.val) (ω : Outcome n) :
    restr k j (info j ω) = info k ω := by
  unfold restr info
  simp only [dif_pos h]

noncomputable def Fq {n : ℕ} (q : Policy n) (j : Fin n) (x : Info n j) : ℝ :=
  q j x * ∏ k ∈ filt j, (1 - q k (restr k j x))

lemma sg_eq_Fq {n : ℕ} (q : Policy n) (j : Fin n) (ω : Outcome n) :
    sg q j ω = Fq q j (info j ω) := by
  unfold sg Fq
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [mem_filt] at hk
  rw [restr_info k j hk.le]

/-- the LP variable induced by a policy -/
noncomputable def zq {n : ℕ} (p' : ℝ) (q : Policy n) (i : Fin n) (s : Bool) : ℝ :=
  Ez n p' i s (sg q i)

lemma signalLaw_top {n : ℕ} (p p' : ℝ) (r : Fin n) (h : r.val + 1 = n) (s : Bool) :
    signalLaw n p p' r s = Tl p s := by
  unfold signalLaw Tl; rw [if_pos h]

lemma signalLaw_ntop {n : ℕ} (p p' : ℝ) (r : Fin n) (h : ¬ r.val + 1 = n) (s : Bool) :
    signalLaw n p p' r s = Nl p' s := by
  unfold signalLaw Nl; rw [if_neg h]

lemma weight_top (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ) (i : Fin n) (ω : Outcome n) :
    weight n p p' ω * (if isTop ω i then (1:ℝ) else 0) =
      ∑ s : Bool, Tl p s / n * ((1 / ((n - 1).factorial : ℝ)) * ezw n p' i s ω) := by
  unfold ezw
  by_cases h : (ω.1 i).val + 1 = n
  · have ht : isTop ω i := h
    rw [if_pos ht, mul_one]
    simp only [if_pos h]
    unfold weight
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), signalLaw_top p p' _ h]
    have hrest : ∏ k ∈ Finset.univ.erase i, signalLaw n p p' (ω.1 k) (ω.2 k) =
        ∏ k ∈ Finset.univ.erase i, Nl p' (ω.2 k) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      apply signalLaw_ntop
      intro h2
      apply hki
      apply ω.1.injective
      apply Fin.ext
      omega
    rw [hrest, Fintype.sum_bool]
    unfold nu
    have hfac : (n.factorial : ℝ) = n * ((n - 1).factorial : ℝ) := by
      have : n = (n - 1) + 1 := by omega
      conv_lhs => rw [this, Nat.factorial_succ]
      push_cast
      congr 1
      exact_mod_cast (show n - 1 + 1 = n by omega)
    rw [hfac]
    have hn0 : (n : ℝ) ≠ 0 := by have : (1:ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
    have hf0 : ((n - 1).factorial : ℝ) ≠ 0 := by positivity
    cases hs : ω.2 i <;> simp <;> field_simp
  · have ht : ¬ isTop ω i := h
    rw [if_neg ht]
    simp [h]

lemma win_eq (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ) (q : Policy n) :
    win p p' q = ∑ i : Fin n, ∑ s : Bool, Tl p s / n * zq p' q i s := by
  unfold win
  have e1 : ∀ ω : Outcome n, weight n p p' ω * ∑ i : Fin n,
      (if isTop ω i then (1:ℝ) else 0) * q i (info i ω) *
        ∏ j ∈ (Finset.univ.filter (fun j : Fin n => j.val < i.val)), (1 - q j (info j ω)) =
      ∑ i : Fin n, (weight n p p' ω * (if isTop ω i then (1:ℝ) else 0)) * sg q i ω := by
    intro ω
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    unfold sg filt; ring
  rw [Finset.sum_congr rfl (fun ω _ => e1 ω), Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  simp only [weight_top n hn p p' i, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  unfold zq Ez
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro ω _
  ring

lemma zq_feasible (n : ℕ) (p' : ℝ) (h0 : 0 ≤ p') (h1 : p' ≤ 1) (q : Policy n)
    (hq : ValidPolicy q) (i : Fin n) (s : Bool) :
    0 ≤ zq p' q i s ∧
    zq p' q i s ≤ 1 - ∑ j ∈ filt i, ∑ s' : Bool, chat (j.val + 1) p' s' * zq p' q j s' := by
  refine ⟨Ez_nonneg n p' h0 h1 i s _ (sg_nonneg q hq i), ?_⟩
  unfold zq
  calc Ez n p' i s (sg q i)
      ≤ Ez n p' i s (fun ω => 1 - ∑ j ∈ filt i, sg q j ω) :=
        Ez_mono n p' h0 h1 i s _ _ (sg_le q hq i)
    _ = 1 - ∑ j ∈ filt i, Ez n p' i s (sg q j) := by
        rw [Ez_sub n p' i s (fun _ => 1) (fun ω => ∑ j ∈ filt i, sg q j ω), Ez_one,
          Ez_sum (filt i) n p' i s (fun j ω => sg q j ω)]
    _ ≤ 1 - ∑ j ∈ filt i, Ez n p' i s
          (fun ω => if bestSoFar j (info j ω) then Fq q j (info j ω) else 0) := by
        apply sub_le_sub_left
        apply Finset.sum_le_sum
        intro j _
        apply Ez_mono n p' h0 h1 i s
        intro ω
        split_ifs
        · rw [sg_eq_Fq]
        · exact sg_nonneg q hq j ω
    _ = 1 - ∑ j ∈ filt i, ∑ s' : Bool, chat (j.val + 1) p' s' * Ez n p' j s' (sg q j) := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [mem_filt] at hj
        rw [lemA n p' i j hj s (Fq q j)]
        apply Finset.sum_congr rfl
        intro s' _
        congr 2
        funext ω
        rw [sg_eq_Fq]

lemma thr_valid (n tY tN : ℕ) : ValidPolicy (thresholdPolicy n tY tN) := by
  intro i x
  unfold thresholdPolicy
  split_ifs <;> norm_num

lemma thr_zero {n : ℕ} (tY tN : ℕ) (j : Fin n) (x : Info n j) (h : ¬ bestSoFar j x) :
    thresholdPolicy n tY tN j x = 0 := by
  unfold thresholdPolicy
  rw [if_neg (fun h' => h h'.1)]

lemma thr_top {n : ℕ} (tY tN : ℕ) (i : Fin n) (ω : Outcome n) (h : (ω.1 i).val + 1 = n) :
    thresholdPolicy n tY tN i (info i ω) =
      if (if ω.2 i then tY else tN) ≤ i.val + 1 then 1 else 0 := by
  have hb : bestSoFar i (info i ω) := by
    intro a
    show decide (ω.1 ⟨a.val, by omega⟩ ≤ ω.1 ⟨(Fin.last i.val).val, by omega⟩) = true
    rw [decide_eq_true_eq]
    have e : (⟨(Fin.last i.val).val, by omega⟩ : Fin n) = i := by
      apply Fin.ext; simp
    rw [e]
    show (ω.1 ⟨a.val, _⟩).val ≤ (ω.1 i).val
    have := (ω.1 ⟨a.val, by omega⟩).isLt
    omega
  have hs : (info i ω).2 (Fin.last i.val) = ω.2 i := by
    show ω.2 ⟨(Fin.last i.val).val, by omega⟩ = ω.2 i
    congr 1
  unfold thresholdPolicy
  rw [hs]
  by_cases hc : (if ω.2 i then tY else tN) ≤ i.val + 1
  · rw [if_pos ⟨hb, hc⟩, if_pos hc]
  · rw [if_neg (fun h' => hc h'.2), if_neg hc]

lemma zthr_formula (n : ℕ) (p' : ℝ) (tY tN : ℕ) (i : Fin n) (s : Bool) :
    zq p' (thresholdPolicy n tY tN) i s =
      (if (if s then tY else tN) ≤ i.val + 1 then 1 else 0) *
      (1 - ∑ j ∈ filt i, ∑ s' : Bool, chat (j.val + 1) p' s' *
        zq p' (thresholdPolicy n tY tN) j s') := by
  set c : ℝ := if (if s then tY else tN) ≤ i.val + 1 then 1 else 0 with hc
  unfold zq
  have h1 : Ez n p' i s (sg (thresholdPolicy n tY tN) i) =
      Ez n p' i s (fun ω => c * (1 - ∑ j ∈ filt i, sg (thresholdPolicy n tY tN) j ω)) := by
    apply Ez_congr
    intro ω htop hs
    have e : sg (thresholdPolicy n tY tN) i ω = thresholdPolicy n tY tN i (info i ω) *
        ∏ j ∈ filt i, (1 - thresholdPolicy n tY tN j (info j ω)) := rfl
    rw [e, sg_tele, thr_top tY tN i ω htop, hs]
  rw [h1, Ez_const_mul, Ez_sub n p' i s (fun _ => 1)
    (fun ω => ∑ j ∈ filt i, sg (thresholdPolicy n tY tN) j ω), Ez_one,
    Ez_sum (filt i) n p' i s (fun j ω => sg (thresholdPolicy n tY tN) j ω)]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [mem_filt] at hj
  have h2 : sg (thresholdPolicy n tY tN) j = fun ω => if bestSoFar j (info j ω) then
      Fq (thresholdPolicy n tY tN) j (info j ω) else 0 := by
    funext ω
    split_ifs with hb
    · rw [sg_eq_Fq]
    · unfold sg; rw [thr_zero tY tN j _ hb, zero_mul]
  have h3 : Ez n p' i s (sg (thresholdPolicy n tY tN) j) = Ez n p' i s (fun ω =>
      if bestSoFar j (info j ω) then Fq (thresholdPolicy n tY tN) j (info j ω) else 0) := by
    rw [h2]
  rw [h3, lemA n p' i j hj s (Fq (thresholdPolicy n tY tN) j)]
  apply Finset.sum_congr rfl
  intro s' _
  congr 2
  funext ω
  rw [sg_eq_Fq]

/-- transport a round-indexed table to the LP's 1-based indexing -/
noncomputable def Zof {n : ℕ} (z : Fin n → Bool → ℝ) : ℕ → Bool → ℝ :=
  fun k s => if h : 1 ≤ k ∧ k ≤ n then z ⟨k - 1, by omega⟩ s else 0

lemma Zof_succ {n : ℕ} (z : Fin n → Bool → ℝ) (i : Fin n) (s : Bool) :
    Zof z (i.val + 1) s = z i s := by
  unfold Zof
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1

lemma icc_fin (n : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 n, g k = ∑ i : Fin n, g (i.val + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => g (k + 1)) n]
  have : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [this, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl; intro k _; rw [add_comm]

lemma primal_Zof (n : ℕ) (p : ℝ) (z : Fin n → Bool → ℝ) :
    primalValue n p (Zof z) = ∑ i : Fin n, ∑ s : Bool, Tl p s / n * z i s := by
  unfold primalValue
  rw [icc_fin n]
  apply Finset.sum_congr rfl; intro i _
  rw [Zof_succ, Zof_succ, Fintype.sum_bool]
  unfold Tl; simp; ring

lemma Cfun_Zof (n : ℕ) (p' : ℝ) (z : Fin n → Bool → ℝ) (i : Fin n) :
    Cfun p' (Zof z) (i.val + 1) = ∑ j ∈ filt i, ∑ s' : Bool, chat (j.val + 1) p' s' * z j s' := by
  unfold Cfun
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have := filt_sum i (fun k => chat (1 + k) p' true * Zof z (1 + k) true +
    chat (1 + k) p' false * Zof z (1 + k) false)
  rw [← this]
  apply Finset.sum_congr rfl; intro j _
  rw [Fintype.sum_bool, add_comm 1 j.val, Zof_succ, Zof_succ]

end SA4

open SA4 in
theorem solution (n : ℕ) (hn : 1 ≤ n) (p p' : ℝ)
    (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1)
    (hp'0 : (1 / 2 : ℝ) ≤ p') (hp'1 : p' ≤ 1)
    (hopt : DualFeasible n p p' (greedy n p p') ∧
      ∀ u : ℕ → Bool → ℝ, DualFeasible n p p' u →
        dualValue n (greedy n p p') ≤ dualValue n u)
    (hmono : ∀ i : ℕ, 1 ≤ i → i < n → ∀ s : Bool,
      greedy n p p' i s ≤ greedy n p p' (i + 1) s) :
    ∃ tY tN : ℕ, 1 ≤ tY ∧ tY ≤ n ∧ 1 ≤ tN ∧ tN ≤ n ∧
      ∀ q : Policy n, ValidPolicy q →
        win p p' q ≤ win p p' (thresholdPolicy n tY tN) := by
  obtain ⟨tY, tN, h1, h2, h3, h4, hthr⟩ := thr_lp n hn p p' hp0 hp1 hmono
  refine ⟨tY, tN, h1, h2, h3, h4, fun q hq => ?_⟩
  have h0' : 0 ≤ p' := by linarith
  rw [win_eq n hn p p' q, win_eq n hn p p' (thresholdPolicy n tY tN),
    ← primal_Zof, ← primal_Zof]
  have hle : primalValue n p (Zof (zq p' q)) ≤ dualValue n (greedy n p p') := by
    apply lp_le n p p' _ _ _ hopt.1
    intro k hk1 hk2 s
    have hk : k = (⟨k - 1, by omega⟩ : Fin n).val + 1 := by simp; omega
    rw [hk, Zof_succ, Cfun_Zof]
    exact zq_feasible n p' h0' hp'1 q hq _ s
  have heq : primalValue n p (Zof (zq p' (thresholdPolicy n tY tN))) =
      dualValue n (greedy n p p') := by
    apply hthr
    intro k hk1 hk2 s
    have hk : k = (⟨k - 1, by omega⟩ : Fin n).val + 1 := by simp; omega
    rw [hk, Zof_succ, Cfun_Zof, zthr_formula]
    split_ifs <;> ring
  linarith


