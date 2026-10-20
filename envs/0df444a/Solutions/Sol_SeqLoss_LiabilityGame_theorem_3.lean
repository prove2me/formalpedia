-- Prove2me | solution 1 for SeqLoss.LiabilityGame.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T18:36:13.086977+00:00
-- url     : https://prove2.me/submissions/ef7ff43b-4b73-4cbc-bb20-aa29de100f4c

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_SeqLoss_FixedFraction_Setting
import Definitions.Def_SeqLoss_LiabilityGame_Game
import Definitions.Def_SeqLoss_LiabilityGame_Nucleolus

set_option autoImplicit false

namespace SeqLossT3

/-- Sorted (non-increasing) lists: equal strict upper parts at level `t` and more copies of `t`
in the second list give a strict lexicographic comparison. -/
theorem lex_of_filter_count (t : ℝ) :
    ∀ (l1 l2 : List ℝ), l1.Pairwise (· ≥ ·) → l2.Pairwise (· ≥ ·) → l1.length = l2.length →
    (l1.filter (fun x => decide (t < x))).Perm (l2.filter (fun x => decide (t < x))) →
    l1.count t < l2.count t → List.Lex (· < ·) l1 l2
  | [], l2, _, _, hlen, _, hc => by
    cases l2 with
    | nil => simp at hc
    | cons _ _ => simp at hlen
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen
  | a :: l1, b :: l2, h1, h2, hlen, hf, hc => by
    rw [List.pairwise_cons] at h1 h2
    by_cases ha : t < a
    · have haf : a ∈ (b :: l2).filter (fun x => decide (t < x)) := by
        rw [← hf.mem_iff]; simp [ha]
      have hab : a ≤ b := by
        simp only [List.mem_filter, List.mem_cons] at haf
        rcases haf.1 with h | h
        · exact h.le
        · exact h2.1 a h
      have hb : t < b := lt_of_lt_of_le ha hab
      have hbf : b ∈ (a :: l1).filter (fun x => decide (t < x)) := by
        rw [hf.mem_iff]; simp [hb]
      have hba : b ≤ a := by
        simp only [List.mem_filter, List.mem_cons] at hbf
        rcases hbf.1 with h | h
        · exact h.le
        · exact h1.1 b h
      have heq : a = b := le_antisymm hab hba
      subst heq
      apply List.Lex.cons
      have hne : a ≠ t := ne_of_gt ha
      apply lex_of_filter_count t l1 l2 h1.2 h2.2 (by simpa using hlen)
      · simp only [List.filter_cons, ha, decide_true, if_true] at hf
        exact hf.cons_inv
      · rw [List.count_cons, List.count_cons] at hc
        simp only [beq_iff_eq, hne, if_false] at hc
        simpa using hc
    · push Not at ha
      have hf1 : (a :: l1).filter (fun x => decide (t < x)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        simp only [List.mem_cons] at hx
        have : x ≤ t := by
          rcases hx with h | h
          · exact h ▸ ha
          · exact (h1.1 x h).trans ha
        simpa using this
      rw [hf1] at hf
      have hf2 : (b :: l2).filter (fun x => decide (t < x)) = [] := hf.symm.eq_nil
      have hbt : b ≤ t := by
        rw [List.filter_eq_nil_iff] at hf2
        simpa using hf2 b (by simp)
      have htmem : t ∈ b :: l2 := List.count_pos_iff.mp (lt_of_le_of_lt (Nat.zero_le _) hc)
      have htb : t ≤ b := by
        simp only [List.mem_cons] at htmem
        rcases htmem with h | h
        · exact h.le
        · exact h2.1 t h
      have hbeq : b = t := le_antisymm hbt htb
      subst hbeq
      rcases lt_or_eq_of_le ha with hlt | hEq
      · exact List.Lex.rel hlt
      · subst hEq
        apply List.Lex.cons
        apply lex_of_filter_count a l1 l2 h1.2 h2.2 (by simpa using hlen)
        · have e1 : l1.filter (fun x => decide (a < x)) = [] := by
            rw [List.filter_eq_nil_iff] at hf1 ⊢
            intro x hx; exact hf1 x (by simp [hx])
          have e2 : l2.filter (fun x => decide (a < x)) = [] := by
            rw [List.filter_eq_nil_iff] at hf2 ⊢
            intro x hx; exact hf2 x (by simp [hx])
          rw [e1, e2]
        · rw [List.count_cons_self, List.count_cons_self] at hc
          omega

/-- Abstract spreading lemma: `f` complement-symmetric, `g` complement-antisymmetric and
nonzero somewhere; then the sorted values of `f` are lexicographically below those of `f - g`. -/
theorem lex_spread {ι : Type*} [Fintype ι] (c : ι → ι) (f g : ι → ℝ)
    (hf : ∀ S, f (c S) = f S) (hg : ∀ S, g (c S) = - g S) (hne : ∃ S, g S ≠ 0) :
    List.Lex (· < ·) (((Finset.univ : Finset ι).val.map f).sort (· ≥ ·))
      (((Finset.univ : Finset ι).val.map (fun S => f S - g S)).sort (· ≥ ·)) := by
  classical
  set P : Finset ι := Finset.univ.filter (fun S => g S ≠ 0) with hP
  have hPne : P.Nonempty := by
    obtain ⟨S, hS⟩ := hne
    exact ⟨S, by simp [hP, hS]⟩
  set t : ℝ := P.sup' hPne (fun S => f S - g S) with ht
  have key : ∀ S, g S ≠ 0 → f S + |g S| ≤ t := by
    intro S hS
    have h1 : f S - g S ≤ t := Finset.le_sup' (fun S => f S - g S) (by simp [hP, hS])
    have hcS : g (c S) ≠ 0 := by rw [hg]; exact neg_ne_zero.mpr hS
    have h2 : f (c S) - g (c S) ≤ t := Finset.le_sup' (fun S => f S - g S) (by simp [hP, hcS])
    rw [hf, hg] at h2
    rcases abs_cases (g S) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  have small : ∀ S, g S ≠ 0 → f S < t ∧ f S - g S ≤ t := by
    intro S hS
    have := key S hS
    have hpos : 0 < |g S| := abs_pos.mpr hS
    constructor
    · linarith
    · have : -g S ≤ |g S| := neg_le_abs (g S)
      linarith
  obtain ⟨S0, hS0P, hS0⟩ := Finset.exists_mem_eq_sup' hPne (fun S => f S - g S)
  have hS0g : g S0 ≠ 0 := by simpa [hP] using hS0P
  apply lex_of_filter_count t
  · exact Multiset.pairwise_sort _ _
  · exact Multiset.pairwise_sort _ _
  · simp [Multiset.length_sort]
  · apply Multiset.coe_eq_coe.mp
    rw [← Multiset.filter_coe, ← Multiset.filter_coe, Multiset.sort_eq, Multiset.sort_eq,
      Multiset.filter_map, Multiset.filter_map]
    have hcongr : Multiset.filter (LT.lt t ∘ f) Finset.univ.val =
        Multiset.filter (LT.lt t ∘ fun S => f S - g S) Finset.univ.val := by
      apply Multiset.filter_congr
      intro S _
      simp only [Function.comp]
      by_cases hS : g S = 0
      · simp [hS]
      · have := small S hS
        constructor <;> intro h <;> linarith [this.1, this.2]
    rw [hcongr]
    apply Multiset.map_congr rfl
    intro S hS
    rw [Multiset.mem_filter] at hS
    have hS' : t < f S - g S := by simpa using hS.2
    by_cases hgS : g S = 0
    · simp [hgS]
    · have := small S hgS
      linarith [this.2]
  · rw [← Multiset.coe_count, ← Multiset.coe_count, Multiset.sort_eq, Multiset.sort_eq,
      Multiset.count_map, Multiset.count_map]
    have e1 : (Multiset.filter (fun a => t = f a) Finset.univ.val) =
        (Finset.univ.filter (fun a => t = f a)).val := by simp [Finset.filter_val]
    have e2 : (Multiset.filter (fun a => t = f a - g a) Finset.univ.val) =
        (Finset.univ.filter (fun a => t = f a - g a)).val := by simp [Finset.filter_val]
    rw [e1, e2, Finset.card_val, Finset.card_val]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨S0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [ht]; exact hS0
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        have := (small S0 hS0g).1
        linarith
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      by_cases hgS : g S = 0
      · simp [hgS, hS]
      · have := (small S hgS).1
        linarith

open SeqLoss.LiabilityGame SeqLoss.FixedFraction

theorem val_zero_iff {n : ℕ} [NeZero n] (i : Fin n) : i.val = 0 ↔ i = 0 := by
  rw [Fin.ext_iff, Fin.val_zero]

theorem sum_phi {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ i ∈ S, fixedFraction (1 / 2) n ℓ i =
      1 / 2 * ∑ i ∈ S, ℓ i + if (0 : Fin n) ∈ S then 1 / 2 * ∑ j, ℓ j else 0 := by
  have h : ∀ i : Fin n, fixedFraction (1 / 2) n ℓ i =
      1 / 2 * ℓ i + if i = 0 then 1 / 2 * ∑ j, ℓ j else 0 := by
    intro i
    unfold fixedFraction
    by_cases hi : i = 0
    · subst hi
      norm_num
    · have hv : i.val ≠ 0 := fun h => hi ((val_zero_iff i).mp h)
      simp [hi, hv]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq']

theorem excess_phi_compl {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (S : Finset (Fin n)) :
    excess (liabilityGame ℓ) (fixedFraction (1 / 2) n ℓ) Sᶜ =
      excess (liabilityGame ℓ) (fixedFraction (1 / 2) n ℓ) S := by
  unfold excess liabilityGame
  rw [sum_phi, sum_phi]
  have hsum := Finset.sum_compl_add_sum S ℓ
  by_cases h0 : (0 : Fin n) ∈ S
  · have h0' : (0 : Fin n) ∉ Sᶜ := by simp [h0]
    simp only [h0, h0', if_true, if_false]
    linarith
  · have h0' : (0 : Fin n) ∈ Sᶜ := by simp [h0]
    simp only [h0, h0', if_true, if_false]
    linarith

theorem phi_total {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) :
    ∑ i, fixedFraction (1 / 2) n ℓ i = ∑ i, ℓ i := by
  rw [sum_phi]
  simp only [Finset.mem_univ, if_true]
  ring

theorem game_univ {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) :
    liabilityGame ℓ Finset.univ = ∑ i, ℓ i := by
  simp [liabilityGame]

theorem strict {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (y : Fin n → ℝ)
    (hy : IsImputation (liabilityGame ℓ) y) (hne : y ≠ fixedFraction (1 / 2) n ℓ) :
    List.Lex (· < ·) (excessVector (liabilityGame ℓ) (fixedFraction (1 / 2) n ℓ))
      (excessVector (liabilityGame ℓ) y) := by
  set φ := fixedFraction (1 / 2) n ℓ with hφ
  set g : Finset (Fin n) → ℝ := fun S => ∑ i ∈ S, (y i - φ i) with hgdef
  have hey : excess (liabilityGame ℓ) y =
      fun S => excess (liabilityGame ℓ) φ S - g S := by
    funext S
    simp only [excess, hgdef, Finset.sum_sub_distrib]
    ring
  unfold excessVector
  rw [hey]
  apply lex_spread (fun S => Sᶜ)
  · intro S; exact excess_phi_compl ℓ S
  · intro S
    have htot : ∑ i, (y i - φ i) = 0 := by
      rw [Finset.sum_sub_distrib, hy.1, game_univ, hφ, phi_total]; ring
    have := Finset.sum_compl_add_sum S (fun i => y i - φ i)
    simp only [hgdef]
    linarith
  · by_contra hall
    push Not at hall
    apply hne
    funext i
    have := hall {i}
    simp only [hgdef, Finset.sum_singleton] at this
    linarith

theorem phi_imputation {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (hℓ : IsLoss ℓ) :
    IsImputation (liabilityGame ℓ) (fixedFraction (1 / 2) n ℓ) := by
  refine ⟨by rw [phi_total, game_univ], ?_⟩
  intro i
  by_cases hi : i = 0
  · subst hi
    have hle : ℓ 0 ≤ ∑ j, ℓ j :=
      Finset.single_le_sum (fun j _ => hℓ j) (Finset.mem_univ _)
    simp [liabilityGame, fixedFraction]
    linarith
  · have hi' : (0 : Fin n) ∉ ({i} : Finset (Fin n)) := by
      simp [Ne.symm hi]
    have hiv : i.val ≠ 0 := fun h => hi ((val_zero_iff i).mp h)
    simp only [liabilityGame, hi', if_false, fixedFraction, hiv]
    have := hℓ i
    linarith

/-- Shapley weight sum. -/
theorem weight_total {n : ℕ} [NeZero n] (i : Fin n) :
    ∑ S ∈ (Finset.univ.erase i).powerset,
      ((S.card.factorial * (n - S.card - 1).factorial : ℝ) / n.factorial) = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have hcard : (Finset.univ.erase i).card = m := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  rw [Finset.sum_powerset_apply_card
    (fun k => ((k.factorial * (m + 1 - k - 1).factorial : ℝ) / (m + 1).factorial)), hcard]
  have hterm : ∀ k ∈ Finset.range (m + 1),
      (m.choose k) • ((k.factorial * (m + 1 - k - 1).factorial : ℝ) / (m + 1).factorial) =
        (m.factorial : ℝ) / (m + 1).factorial := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : m + 1 - k - 1 = m - k := by omega
    rw [hsub, nsmul_eq_mul, ← mul_div_assoc]
    congr 1
    have := Nat.choose_mul_factorial_mul_factorial hk'
    rw [← this]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.factorial_succ]
  push_cast
  have : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Half the weight sits on coalitions containing a fixed other player `j`. -/
theorem weight_half {n : ℕ} [NeZero n] (i j : Fin n) (hij : i ≠ j) :
    ∑ S ∈ (Finset.univ.erase i).powerset,
      (if j ∈ S then ((S.card.factorial * (n - S.card - 1).factorial : ℝ) / n.factorial)
        else 0) = 1 / 2 := by
  set M := Finset.univ.erase i with hM
  set w : ℕ → ℝ := fun k => (k.factorial * (n - k - 1).factorial : ℝ) / n.factorial with hw
  have hjM : j ∈ M := by simp [hM, Ne.symm hij]
  have hcardM : M.card = n - 1 := by
    rw [hM, Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  have hsymm : ∀ S ∈ M.powerset, w (M \ S).card = w S.card := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hc : (M \ S).card = M.card - S.card := Finset.card_sdiff_of_subset hS
    have hle : S.card ≤ M.card := Finset.card_le_card hS
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    simp only [hw, hc, hcardM]
    rw [hcardM] at hle
    have e1 : n - (n - 1 - S.card) - 1 = S.card := by omega
    rw [e1]
    have e2 : n - 1 - S.card = n - S.card - 1 := by omega
    rw [e2]
    ring
  have hswap : ∑ S ∈ M.powerset, (if j ∈ S then w S.card else 0) =
      ∑ S ∈ M.powerset, (if j ∈ S then 0 else w S.card) := by
    apply Finset.sum_nbij' (fun S => M \ S) (fun S => M \ S)
    · intro S hS; simp [Finset.mem_powerset]
    · intro S hS; simp [Finset.mem_powerset]
    · intro S hS
      exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (by simpa using hS))
    · intro S hS
      exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp (by simpa using hS))
    · intro S hS
      have hS' : S ∈ M.powerset := by simpa using hS
      have : j ∈ M \ S ↔ j ∉ S := by simp [Finset.mem_sdiff, hjM]
      by_cases hjS : j ∈ S
      · have : j ∉ M \ S := by simp [Finset.mem_sdiff, hjS]
        simp [hjS, this, hsymm S hS']
      · have : j ∈ M \ S := by simp [Finset.mem_sdiff, hjS, hjM]
        simp [hjS, this]
  have htot : ∑ S ∈ M.powerset, w S.card = 1 := weight_total i
  have hsplit : ∑ S ∈ M.powerset, w S.card =
      ∑ S ∈ M.powerset, (if j ∈ S then w S.card else 0) +
        ∑ S ∈ M.powerset, (if j ∈ S then 0 else w S.card) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp
  show ∑ S ∈ M.powerset, (if j ∈ S then w S.card else 0) = 1 / 2
  linarith

theorem shapley {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) :
    Supermodularity.Cooperative.ShapleyValue (liabilityGame ℓ) =
      fixedFraction (1 / 2) n ℓ := by
  funext i
  unfold Supermodularity.Cooperative.ShapleyValue
  set w : ℕ → ℝ := fun k => (k.factorial * (n - k - 1).factorial : ℝ) / n.factorial with hw
  by_cases hi : i = 0
  · subst hi
    set M := (Finset.univ : Finset (Fin n)).erase 0 with hM
    have hstep : ∀ S ∈ M.powerset,
        w S.card * (liabilityGame ℓ (insert 0 S) - liabilityGame ℓ S) =
          ℓ 0 * w S.card + ∑ j ∈ M, (if j ∈ S then w S.card else 0) * ℓ j := by
      intro S hS
      have hSM : S ⊆ M := Finset.mem_powerset.mp hS
      have h0S : (0 : Fin n) ∉ S := fun h => by simpa [hM] using hSM h
      have hsumS : ∑ j ∈ M, (if j ∈ S then w S.card else 0) * ℓ j =
          w S.card * ∑ j ∈ S, ℓ j := by
        rw [Finset.mul_sum]
        have : ∑ j ∈ M, (if j ∈ S then w S.card else 0) * ℓ j =
            ∑ j ∈ M, (if j ∈ S then w S.card * ℓ j else 0) := by
          apply Finset.sum_congr rfl; intro j _; split_ifs <;> simp
        rw [this, ← Finset.sum_filter]
        congr 1
        ext j; simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hSM h, h⟩⟩
      rw [hsumS]
      simp only [liabilityGame, Finset.mem_insert_self, if_true, h0S, if_false,
        Finset.sum_insert h0S]
      ring
    show ∑ S ∈ M.powerset, w S.card * (liabilityGame ℓ (insert 0 S) - liabilityGame ℓ S) = _
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    have hw1 : ∑ S ∈ M.powerset, w S.card = 1 := weight_total 0
    have hwj : ∀ j ∈ M, ∑ S ∈ M.powerset, (if j ∈ S then w S.card else 0) * ℓ j =
        1 / 2 * ℓ j := by
      intro j hj
      rw [← Finset.sum_mul]
      have hj0 : (0 : Fin n) ≠ j := fun h => by simp [hM, ← h] at hj
      rw [weight_half 0 j hj0]
    rw [Finset.sum_congr rfl hwj, hw1, ← Finset.mul_sum]
    have hL : ∑ j, ℓ j = ℓ 0 + ∑ j ∈ M, ℓ j := by
      rw [hM, Finset.add_sum_erase _ _ (Finset.mem_univ _)]
    simp only [fixedFraction, Fin.val_zero, if_true]
    rw [hL]
    ring
  · set M := (Finset.univ : Finset (Fin n)).erase i with hM
    have hstep : ∀ S ∈ M.powerset,
        w S.card * (liabilityGame ℓ (insert i S) - liabilityGame ℓ S) =
          (if (0 : Fin n) ∈ S then w S.card else 0) * ℓ i := by
      intro S hS
      have hSM : S ⊆ M := Finset.mem_powerset.mp hS
      have hiS : i ∉ S := fun h => by simpa [hM] using hSM h
      have hmem : (0 : Fin n) ∈ insert i S ↔ (0 : Fin n) ∈ S := by
        rw [Finset.mem_insert]
        exact ⟨fun h => h.resolve_left (Ne.symm hi), Or.inr⟩
      by_cases h0 : (0 : Fin n) ∈ S
      · have h0' : (0 : Fin n) ∈ insert i S := hmem.mpr h0
        simp only [liabilityGame, h0, h0', if_true, Finset.sum_insert hiS]
        ring
      · have h0' : (0 : Fin n) ∉ insert i S := fun h => h0 (hmem.mp h)
        simp only [liabilityGame, h0, h0', if_false]
        ring
    show ∑ S ∈ M.powerset, w S.card * (liabilityGame ℓ (insert i S) - liabilityGame ℓ S) = _
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, weight_half i 0 hi]
    have hiv : i.val ≠ 0 := fun h => hi ((val_zero_iff i).mp h)
    simp only [fixedFraction, hiv, if_false]
    ring

end SeqLossT3

open SeqLoss.LiabilityGame in
theorem solution {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) (hℓ : SeqLoss.FixedFraction.IsLoss ℓ) :
    Supermodularity.Cooperative.ShapleyValue (liabilityGame ℓ) = SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ ∧
    IsNucleolus (liabilityGame ℓ) (SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ) ∧
    ∀ x : Fin n → ℝ, IsNucleolus (liabilityGame ℓ) x → x = SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ := by
  refine ⟨SeqLossT3.shapley ℓ, ⟨SeqLossT3.phi_imputation ℓ hℓ, ?_⟩, ?_⟩
  · intro y hy hlex
    by_cases hyφ : y = SeqLoss.FixedFraction.fixedFraction (1 / 2) n ℓ
    · subst hyφ
      exact _root_.asymm hlex hlex
    · exact _root_.asymm hlex (SeqLossT3.strict ℓ y hy hyφ)
  · intro x hx
    by_contra hne
    exact hx.2 _ (SeqLossT3.phi_imputation ℓ hℓ) (SeqLossT3.strict ℓ x hx.1 hne)
