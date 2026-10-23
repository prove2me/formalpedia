-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P06.classicalTwirl_agreement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:56:50.121321+00:00
-- url     : https://prove2.me/submissions/a7b1a943-10e8-4aa1-bc3b-251d8d3fc0e4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P06

open scoped BigOperators

lemma x8_two_trans {d : ℕ} [NeZero d] (hd : 2 ≤ d) (a b : ZMod d) (hab : b ≠ a) :
    ∃ τ : Equiv.Perm (ZMod d), τ 0 = a ∧ τ 1 = b := by
  have h10 : (1 : ZMod d) ≠ 0 := by
    have : Fact (1 < d) := ⟨by omega⟩
    exact one_ne_zero
  set c := Equiv.swap (0 : ZMod d) a 1 with hc
  have hca : c ≠ a := by
    intro h
    have : Equiv.swap (0 : ZMod d) a 1 = Equiv.swap (0 : ZMod d) a 0 := by
      rw [← hc, h, Equiv.swap_apply_left]
    exact h10 ((Equiv.swap (0 : ZMod d) a).injective this)
  refine ⟨Equiv.swap c b * Equiv.swap 0 a, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hca) (Ne.symm hab)
  · rw [Equiv.Perm.mul_apply, ← hc, Equiv.swap_apply_left]

lemma x8_twirl {d : ℕ} [NeZero d] (hd : 2 ≤ d) (P : Transition d) (hP : IsClassicalChannel P) :
    classicalTwirl P = symmetricChannel d (classicalAverage P) := by
  set S : ZMod d → ZMod d → ℝ := fun b a => ∑ σ : Equiv.Perm (ZMod d), P (σ b) (σ a) with hS
  have hinv : ∀ (τ : Equiv.Perm (ZMod d)) b a, S (τ b) (τ a) = S b a := by
    intro τ b a
    simp only [hS]
    exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ : Equiv.Perm (ZMod d) => P (σ b) (σ a))
  have hdiag : ∀ a, S a a = S 0 0 := by
    intro a
    have := hinv (Equiv.swap 0 a) 0 0
    rwa [Equiv.swap_apply_left] at this
  have hoff : ∀ a b, b ≠ a → S b a = S 1 0 := by
    intro a b hab
    obtain ⟨τ, h0, h1⟩ := x8_two_trans hd a b hab
    rw [← hinv τ 1 0, h0, h1]
  have hcard : (Fintype.card (Equiv.Perm (ZMod d)) : ℝ) = (Nat.factorial d : ℝ) := by
    rw [Fintype.card_perm, ZMod.card]
  have hcol : ∑ b, S b 0 = Nat.factorial d := by
    simp only [hS]
    rw [Finset.sum_comm]
    have : ∀ σ : Equiv.Perm (ZMod d), ∑ b, P (σ b) (σ 0) = 1 := by
      intro σ
      rw [Equiv.sum_comp σ (fun b => P b (σ 0))]
      exact hP.2 _
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact hcard
  have hdsum : ∑ a, S a a = Nat.factorial d * ∑ c, P c c := by
    simp only [hS]
    rw [Finset.sum_comm]
    have : ∀ σ : Equiv.Perm (ZMod d), ∑ a, P (σ a) (σ a) = ∑ c, P c c := fun σ =>
      Equiv.sum_comp σ (fun c => P c c)
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hfac : (0 : ℝ) < Nat.factorial d := by exact_mod_cast Nat.factorial_pos d
  have hS00 : S 0 0 = Nat.factorial d * classicalAverage P := by
    have h1 : ∑ a, S a a = d * S 0 0 := by
      simp only [hdiag, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [h1] at hdsum
    unfold classicalAverage
    field_simp
    linarith
  have hS10 : S 1 0 = Nat.factorial d * (1 - classicalAverage P) / ((d : ℝ) - 1) := by
    have h1 : ∑ b, S b 0 = S 0 0 + ((d : ℝ) - 1) * S 1 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod d))]
      congr 1
      rw [Finset.sum_congr rfl fun b hb => hoff 0 b (Finset.ne_of_mem_erase hb),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ZMod.card, nsmul_eq_mul]
      have : 1 ≤ d := by omega
      push_cast [this]
      ring
    rw [h1, hS00] at hcol
    field_simp
    linarith
  funext b a
  unfold classicalTwirl symmetricChannel
  split_ifs with hab
  · subst hab
    change (Nat.factorial d : ℝ)⁻¹ * S b b = _
    rw [hdiag, hS00]
    field_simp
  · change (Nat.factorial d : ℝ)⁻¹ * S b a = _
    rw [hoff a b hab, hS10]
    field_simp


lemma x8_branch_sum {d n : ℕ} [NeZero d] (Q : Fin n → Transition d) (k : ZMod d) :
    ∑ j, agreementBranch Q j k = agreementSuccess Q := by
  unfold agreementBranch agreementSuccess
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq']
  simp

lemma x8_branch_nonneg {d n : ℕ} [NeZero d] (Q : Fin n → Transition d)
    (hQ : ∀ i b a, 0 ≤ Q i b a) (j k : ZMod d) : 0 ≤ agreementBranch Q j k := by
  unfold agreementBranch
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_)
  split_ifs
  · exact Finset.prod_nonneg fun i _ => hQ i b a
  · exact le_rfl

lemma x8_branch_diag {d n : ℕ} [NeZero d] (g : Fin n → ℝ) (j : ZMod d) :
    agreementBranch (fun i => symmetricChannel d (g i)) j j = ∏ i, g i := by
  unfold agreementBranch
  have : ∀ a b : ZMod d, (j = j + a - b) ↔ b = a := by
    intro a b
    constructor
    · intro h
      linear_combination h
    · rintro rfl; ring
  simp only [this]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, symmetricChannel]
  simp only [if_true, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  field_simp

lemma x8_succ {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (hn : 1 ≤ n) (g : Fin n → ℝ) :
    agreementSuccess (fun i => symmetricChannel d (g i)) = symmetricSuccess (d : ℝ) g := by
  unfold agreementSuccess symmetricSuccess
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have inner : ∀ a : ZMod d, ∑ b, ∏ i, symmetricChannel d (g i) b a =
      ∏ i, g i + ((d : ℝ) - 1) * (∏ i, (1 - g i)) / ((d : ℝ) - 1) ^ n := by
    intro a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    congr 1
    · simp [symmetricChannel]
    · rw [Finset.sum_congr rfl fun b hb => (show ∏ i, symmetricChannel d (g i) b a =
          (∏ i, (1 - g i)) / ((d : ℝ) - 1) ^ n by
        simp only [symmetricChannel, if_neg (Finset.ne_of_mem_erase hb), Finset.prod_div_distrib,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin])]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ZMod.card, nsmul_eq_mul]
      have : 1 ≤ d := by omega
      push_cast [this]
      ring
  simp only [inner, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ, one_div, inv_pow]
  field_simp

lemma x8_fid_const {d : ℕ} [NeZero d] (Q : Transition d) (c : ℝ) (h : ∀ j, Q j j = c) :
    classicalFidelity Q = c := by
  unfold classicalFidelity
  have : (fun a => Q a a) = fun _ => c := funext h
  rw [this, Set.range_const, csInf_singleton]

lemma x8_fid_le {d : ℕ} [NeZero d] (P : Transition d) (hP : IsClassicalChannel P) :
    classicalFidelity P ≤ classicalAverage P := by
  unfold classicalFidelity classicalAverage
  have hb : BddBelow (Set.range fun a => P a a) := ⟨0, by rintro _ ⟨a, rfl⟩; exact hP.1 a a⟩
  have hle : ∀ a, sInf (Set.range fun a => P a a) ≤ P a a := fun a => csInf_le hb ⟨a, rfl⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hle a
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at this
  rw [le_inv_mul_iff₀ hd0]
  exact this

lemma x8_avg_mem {d : ℕ} [NeZero d] (P : Transition d) (hP : IsClassicalChannel P) :
    0 ≤ classicalAverage P ∧ classicalAverage P ≤ 1 := by
  unfold classicalAverage
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have hle : ∀ a, P a a ≤ 1 := by
    intro a
    rw [← hP.2 a]
    exact Finset.single_le_sum (fun b _ => hP.1 b a) (Finset.mem_univ a)
  refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hP.1 a a), ?_⟩
  have := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hle a
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at this
  rw [inv_mul_le_iff₀ hd0, mul_one]
  exact this


lemma x8_improve {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ≤ n) (f : Fin n → ℝ)
    (hf : ∀ i, 1 / (d : ℝ) < f i ∧ f i < 1) (i : Fin n) :
    f i * symmetricSuccess (d : ℝ) f < ∏ j, f j := by
  unfold symmetricSuccess
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hfpos : ∀ j, 0 < f j := fun j => lt_trans (by positivity) (hf j).1
  set s := Finset.univ.erase i with hs
  have hcard : s.card = n - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  set A := ∏ j ∈ s, f j with hA
  set C := ∏ j ∈ s, (1 / ((d : ℝ) - 1)) * (1 - f j) with hC
  have hPf : ∏ j, f j = f i * A := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hP1 : (1 / ((d : ℝ) - 1)) ^ (n - 1) * ∏ j, (1 - f j) = (1 - f i) * C := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hC, Finset.prod_mul_distrib,
      Finset.prod_const, hcard]
    ring
  have hne : s.Nonempty := by
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
      by_cases h : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega⟩
      · exact ⟨⟨0, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega⟩
    exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩⟩
  have hCA : C < A := by
    refine Finset.prod_lt_prod_of_nonempty (fun j _ => ?_) (fun j _ => ?_) hne
    · have := (hf j).2
      have : 0 < 1 - f j := by linarith
      positivity
    · have h1 := (hf j).1
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < d)] at h1
      rw [one_div, inv_mul_lt_iff₀ hd1]
      nlinarith
  rw [hP1, hPf]
  have h1 : 0 < f i := hfpos i
  have h2 : 0 < 1 - f i := by linarith [(hf i).2]
  have h3 : 0 < A - C := by linarith
  nlinarith [mul_pos (mul_pos h1 h2) h3]

lemma x8_main {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (hn : 2 ≤ n)
    (P : Fin n → Transition d) (hP : ∀ i, IsClassicalChannel (P i)) :
    (∀ i, classicalTwirl (P i) = symmetricChannel d (classicalAverage (P i))) ∧
    agreementSuccess (fun i => classicalTwirl (P i)) =
      symmetricSuccess (d : ℝ) (fun i => classicalAverage (P i)) ∧
    (0 < symmetricSuccess (d : ℝ) (fun i => classicalAverage (P i)) →
      IsClassicalChannel (agreementOutput (fun i => classicalTwirl (P i))) ∧
      classicalFidelity (agreementOutput (fun i => classicalTwirl (P i))) =
        (∏ i, classicalAverage (P i)) /
          symmetricSuccess (d : ℝ) (fun i => classicalAverage (P i))) ∧
    ((∀ i, 1 / (d : ℝ) < classicalAverage (P i) ∧ classicalAverage (P i) < 1) →
      0 < symmetricSuccess (d : ℝ) (fun i => classicalAverage (P i)) ∧
      ∀ i, classicalAverage (P i) <
          classicalFidelity (agreementOutput (fun i => classicalTwirl (P i))) ∧
        classicalFidelity (P i) ≤ classicalAverage (P i)) := by
  set f : Fin n → ℝ := fun i => classicalAverage (P i) with hf
  have hT : (fun i => classicalTwirl (P i)) = fun i => symmetricChannel d (f i) :=
    funext fun i => x8_twirl hd _ (hP i)
  have hsucc := x8_succ hd (by omega) f
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hnn : ∀ i b a, 0 ≤ symmetricChannel d (f i) b a := by
    intro i b a
    have := x8_avg_mem (P i) (hP i)
    unfold symmetricChannel
    split_ifs
    · exact this.1
    · exact div_nonneg (by linarith [this.2]) (by linarith)
  have hfid : 0 < symmetricSuccess (d : ℝ) f →
      classicalFidelity (agreementOutput (fun i => symmetricChannel d (f i))) =
        (∏ i, f i) / symmetricSuccess (d : ℝ) f := by
    intro _
    refine x8_fid_const _ _ fun j => ?_
    unfold agreementOutput
    rw [x8_branch_diag, hsucc]
  rw [hT]
  refine ⟨fun i => x8_twirl hd _ (hP i), hsucc, fun hpos => ⟨⟨?_, ?_⟩, hfid hpos⟩, fun hlt => ?_⟩
  · intro j k
    unfold agreementOutput
    exact div_nonneg (x8_branch_nonneg _ hnn j k) (by rw [hsucc]; exact hpos.le)
  · intro k
    unfold agreementOutput
    rw [← Finset.sum_div, x8_branch_sum, hsucc]
    exact div_self hpos.ne'
  · have hpos : 0 < symmetricSuccess (d : ℝ) f := by
      unfold symmetricSuccess
      have h1 : 0 < ∏ i, f i := Finset.prod_pos fun i _ =>
        lt_trans (by positivity) (hlt i).1
      have h2 : 0 ≤ (1 / ((d : ℝ) - 1)) ^ (n - 1) * ∏ i, (1 - f i) := by
        refine mul_nonneg (pow_nonneg (div_nonneg zero_le_one (by linarith)) _)
          (Finset.prod_nonneg fun i _ => by linarith [(hlt i).2])
      linarith
    refine ⟨hpos, fun i => ⟨?_, x8_fid_le _ (hP i)⟩⟩
    rw [hfid hpos, lt_div_iff₀ hpos]
    exact x8_improve hd hn f hlt i

end QAlgorithms.Papers.Independent.Information100.P06

open QAlgorithms.Papers.Independent.Information100.P06 in
theorem solution
    {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (hn : 2 ≤ n)
    (P : Fin n → Transition d) (hP : ∀ i, IsClassicalChannel (P i)) :
    let f := fun i => classicalAverage (P i)
    let T := fun i => classicalTwirl (P i)
    (∀ i, T i = symmetricChannel d (f i)) ∧
    agreementSuccess T = symmetricSuccess (d : ℝ) f ∧
    (0 < symmetricSuccess (d : ℝ) f →
      IsClassicalChannel (agreementOutput T) ∧
      classicalFidelity (agreementOutput T) =
        (∏ i, f i) / symmetricSuccess (d : ℝ) f) ∧
    ((∀ i, 1 / (d : ℝ) < f i ∧ f i < 1) →
      0 < symmetricSuccess (d : ℝ) f ∧
      ∀ i, f i < classicalFidelity (agreementOutput T) ∧
        classicalFidelity (P i) ≤ f i) :=
  x8_main hd hn P hP
