-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P58.thresholdedMaximumError
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:36:17.12473+00:00
-- url     : https://prove2.me/submissions/01557325-657e-4819-ac95-d3d76e799cd5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

open scoped BigOperators

namespace G54E
open QAlgorithms.Papers.Independent.Information100.P58

/-- two-coordinate marginal count. -/
lemma pair_marginal {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ} {k k' : Fin K} (hk : k ≠ k')
    (F : α → α → ℝ) :
    ∑ C : Fin K → α, F (C k) (C k') =
      (Fintype.card α : ℝ) ^ (K - 2) * ∑ x, ∑ y, F x y := by
  have h1 : ∀ C : Fin K → α, F (C k) (C k') =
      ∑ x, ∑ y, F x y * ((if C k = x then 1 else 0) * (if C k' = y then 1 else 0)) := by
    intro C
    simp [Finset.sum_ite_eq']
  simp_rw [h1]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum]
  rw [mul_comm]
  congr 1
  -- count
  let f : Fin K → α → ℝ := fun j v =>
    if j = k then (if v = x then 1 else 0) else if j = k' then (if v = y then 1 else 0) else 1
  have hprod : ∀ C : Fin K → α, ((if C k = x then (1 : ℝ) else 0) * (if C k' = y then 1 else 0)) =
      ∏ j, f j (C j) := by
    intro C
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hk.symm, Finset.mem_univ k'⟩)]
    have : ∀ j ∈ (Finset.univ.erase k).erase k', f j (C j) = 1 := by
      intro j hj
      have h1 := Finset.ne_of_mem_erase hj
      have h2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
      simp [f, h1, h2]
    rw [Finset.prod_congr rfl this]
    simp [f, hk.symm]
  simp_rw [hprod]
  rw [← Fintype.prod_sum]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hk.symm, Finset.mem_univ k'⟩)]
  have : ∀ j ∈ (Finset.univ.erase k).erase k', ∑ v, f j v = (Fintype.card α : ℝ) := by
    intro j hj
    have h1 := Finset.ne_of_mem_erase hj
    have h2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
    simp [f, h1, h2]
  rw [Finset.prod_congr rfl this, Finset.prod_const]
  have hc : ((Finset.univ.erase k).erase k').card = K - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hk.symm, Finset.mem_univ k'⟩),
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  rw [hc]
  simp [f, hk.symm]

def agr {n d : ℕ} (x y : Word n d) : Finset (Fin n) := Finset.univ.filter (fun i => x i = y i)

lemma pat {n d : ℕ} (p : ℝ) (x y : Word n d) :
    ∑ S : Finset (Fin n), patternWeight n p S * (if ∀ i ∈ S, y i = x i then 1 else 0) =
      p ^ (n - (agr x y).card) := by
  set A := agr x y with hA
  have hiff : ∀ S : Finset (Fin n), (∀ i ∈ S, y i = x i) ↔ S ⊆ A := by
    intro S; constructor
    · intro h i hi; simp [hA, agr, (h i hi).symm]
    · intro h i hi; have := h hi; simp [hA, agr] at this; exact this.symm
  simp_rw [hiff, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun S : Finset (Fin n) => S ⊆ A) = A.powerset := by
    ext S; simp
  rw [hf]
  have hAn : A.card ≤ n := by simpa using Finset.card_le_univ A
  have : ∀ S ∈ A.powerset, patternWeight n p S =
      p ^ (n - A.card) * ((1 - p) ^ S.card * p ^ (A.card - S.card)) := by
    intro S hS
    have hSA : S.card ≤ A.card := Finset.card_le_card (Finset.mem_powerset.mp hS)
    unfold patternWeight
    rw [show n - S.card = (n - A.card) + (A.card - S.card) by omega, pow_add]
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow]
  simp

lemma wsum (n : ℕ) (p : ℝ) : ∑ S : Finset (Fin n), patternWeight n p S = 1 := by
  have h := pat (n := n) (d := 1) p (fun _ => (0 : Fin 1)) (fun _ => 0)
  have hA : agr (n := n) (d := 1) (fun _ => (0 : Fin 1)) (fun _ => 0) = Finset.univ := by
    ext i; simp [agr]
  simp only [hA, Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero] at h
  simpa using h

lemma err_bound {n d M : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (C : Fin M → Word n d) (m : Fin M) :
    1 - deterministicIndividual p C m ≤
      (1 / 2) * ∑ m' ∈ Finset.univ.erase m, p ^ (n - (agr (C m) (C m')).card) := by
  unfold deterministicIndividual
  conv_lhs => rw [← wsum n p]
  rw [← Finset.sum_sub_distrib]
  have hw : ∀ S : Finset (Fin n), 0 ≤ patternWeight n p S := fun S => by
    unfold patternWeight; exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hp0 _)
  have hcard : ∀ S : Finset (Fin n), ((compatible C S m).card : ℝ) =
      1 + ∑ m' ∈ Finset.univ.erase m, (if ∀ i ∈ S, C m' i = C m i then 1 else 0) := by
    intro S
    unfold compatible
    rw [Finset.card_filter, Nat.cast_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
    simp
  have hterm : ∀ S : Finset (Fin n), patternWeight n p S - patternWeight n p S /
      ((compatible C S m).card : ℝ) ≤ (1 / 2) * (patternWeight n p S *
        ∑ m' ∈ Finset.univ.erase m, (if ∀ i ∈ S, C m' i = C m i then 1 else 0)) := by
    intro S
    rw [hcard S]
    set c := ∑ m' ∈ Finset.univ.erase m, (if ∀ i ∈ S, C m' i = C m i then (1 : ℝ) else 0)
    have hcN : c = ((Finset.univ.erase m).filter (fun m' => ∀ i ∈ S, C m' i = C m i)).card := by
      simp only [c]; rw [Finset.sum_boole]
    have hc : 0 ≤ c := by rw [hcN]; positivity
    have hc1 : 0 < 1 + c := by linarith
    rw [div_eq_mul_inv, ← mul_one_sub]
    have : 1 - (1 + c)⁻¹ ≤ (1 / 2) * c := by
      rw [sub_le_iff_le_add, ← sub_le_iff_le_add', inv_eq_one_div, le_div_iff₀ hc1]
      rcases Nat.eq_zero_or_pos ((Finset.univ.erase m).filter (fun m' => ∀ i ∈ S, C m' i = C m i)).card
        with h0 | h0
      · rw [hcN, h0]; norm_num
      · have : (1 : ℝ) ≤ c := by rw [hcN]; exact_mod_cast h0
        nlinarith
    calc patternWeight n p S * (1 - (1 + c)⁻¹) ≤ patternWeight n p S * ((1 / 2) * c) :=
          mul_le_mul_of_nonneg_left this (hw S)
      _ = _ := by ring
  refine (Finset.sum_le_sum fun S _ => hterm S).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m' _ => ?_
  exact pat p (C m) (C m')

lemma sum_rpow_le {ι : Type*} (t : Finset ι) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) {s : ℝ} (hs : 1 ≤ s) :
    ∑ i ∈ t, b i ^ s ≤ (∑ i ∈ t, b i) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Real.zero_rpow (by linarith : s ≠ 0)]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h0 : 0 ≤ ∑ i ∈ t, b i := Finset.sum_nonneg fun i _ => hb i
    calc b a ^ s + ∑ i ∈ t, b i ^ s ≤ b a ^ s + (∑ i ∈ t, b i) ^ s := by linarith
      _ ≤ (b a + ∑ i ∈ t, b i) ^ s := Real.add_rpow_le_rpow_add (hb a) h0 hs

lemma bprod {n d : ℕ} (β : ℝ) (x y : Word n d) :
    β ^ (n - (agr x y).card) = ∏ i, (if x i = y i then 1 else β) := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin n => x i = y i)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  unfold agr; omega

lemma pair_total {n d : ℕ} (β : ℝ) :
    ∑ x : Word n d, ∑ y : Word n d, β ^ (n - (agr x y).card) =
      ((d : ℝ) + ((d : ℝ) * d - d) * β) ^ n := by
  simp_rw [bprod]
  have h1 : ∑ x : Word n d, ∑ y : Word n d, ∏ i, (if x i = y i then (1 : ℝ) else β) =
      ∏ _i : Fin n, ∑ ac : Fin d × Fin d, (if ac.1 = ac.2 then (1 : ℝ) else β) := by
    rw [Fintype.prod_sum, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d) (fun _ => Fin d)).symm
      _ _ (fun _ => rfl)
  rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Fintype.sum_prod_type]
  have : ∀ a : Fin d, ∑ c : Fin d, (if a = c then (1 : ℝ) else β) = 1 + ((d : ℝ) - 1) * β := by
    intro a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    have : ∀ c ∈ Finset.univ.erase a, (if a = c then (1 : ℝ) else β) = β := by
      intro c hc; simp [(Finset.ne_of_mem_erase hc).symm]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [if_true]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; exact (Fin.elim0 a)
    · push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hd.ne')]; ring
  rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

lemma avg_code {n d K : ℕ} (hd : 0 < d) (β : ℝ) :
    ∃ C : Fin K → Word n d, ∑ k, ∑ k' ∈ Finset.univ.erase k, β ^ (n - (agr (C k) (C k')).card) ≤
      (K : ℝ) * (K - 1) * (1 / d + (1 - 1 / d) * β) ^ n := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  by_contra hcon
  push Not at hcon
  have hsum := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Fin K → Word n d))
    (fun C _ => hcon C)
  rw [Finset.sum_comm] at hsum
  have hW : (Fintype.card (Word n d) : ℝ) = (d : ℝ) ^ n := by simp [Fintype.card_fun]
  have key : ∀ k : Fin K, ∑ C : Fin K → Word n d, ∑ k' ∈ Finset.univ.erase k,
      β ^ (n - (agr (C k) (C k')).card) =
      ((K : ℝ) - 1) * ((d : ℝ) ^ n) ^ K * (1 / d + (1 - 1 / d) * β) ^ n := by
    intro k
    rw [Finset.sum_comm]
    have : ∀ k' ∈ Finset.univ.erase k, ∑ C : Fin K → Word n d, β ^ (n - (agr (C k) (C k')).card) =
        ((d : ℝ) ^ n) ^ K * (1 / d + (1 - 1 / d) * β) ^ n := by
      intro k' hk'
      have hne : k ≠ k' := (Finset.ne_of_mem_erase hk').symm
      rw [pair_marginal hne (fun x y => β ^ (n - (agr x y).card)), pair_total, hW]
      have hK : 2 ≤ K := by
        have := Finset.card_le_univ ({k, k'} : Finset (Fin K))
        rw [Finset.card_pair hne, Fintype.card_fin] at this; exact this
      have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      have e1 : ((d : ℝ) + ((d : ℝ) * d - d) * β) = (d : ℝ) ^ 2 * (1 / d + (1 - 1 / d) * β) := by
        field_simp
      rw [e1, mul_pow, ← mul_assoc]
      congr 1
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      have : K = (K - 2) + 2 := by omega
      conv_rhs => rw [this]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · exact absurd k.2 (by omega)
    · push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hK.ne')]; ring
  rw [Finset.sum_congr rfl (fun k _ => key k)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin] at hsum
  have hcard : (Fintype.card (Fin K → Word n d) : ℝ) = ((d : ℝ) ^ n) ^ K := by
    simp
  rw [hcard] at hsum
  linarith


lemma prod_total {n d : ℕ} (h : Fin n → Fin d → Fin d → ℝ) :
    ∑ x : Word n d, ∑ y : Word n d, ∏ i, h i (x i) (y i) = ∏ i, ∑ a, ∑ c, h i a c := by
  have hi : ∀ i, ∑ a, ∑ c, h i a c = ∑ ac : Fin d × Fin d, h i ac.1 ac.2 :=
    fun i => (Fintype.sum_prod_type' (fun a c => h i a c)).symm
  simp_rw [hi]
  rw [Fintype.prod_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d) (fun _ => Fin d)).symm
    _ _ (fun _ => rfl)

lemma avg_gen {n d K : ℕ} (hd : 0 < d) (F : Word n d → Word n d → ℝ) :
    ∃ C : Fin K → Word n d, ∑ k, ∑ k' ∈ Finset.univ.erase k, F (C k) (C k') ≤
      (K : ℝ) * (K - 1) * ((∑ x, ∑ y, F x y) / ((d : ℝ) ^ n) ^ 2) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  by_contra hcon
  push Not at hcon
  have hsum := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Fin K → Word n d))
    (fun C _ => hcon C)
  have hswap : ∑ C : Fin K → Word n d, ∑ k, ∑ k' ∈ Finset.univ.erase k, F (C k) (C k') =
      ∑ k, ∑ C : Fin K → Word n d, ∑ k' ∈ Finset.univ.erase k, F (C k) (C k') := Finset.sum_comm
  rw [hswap] at hsum
  have hW : (Fintype.card (Word n d) : ℝ) = (d : ℝ) ^ n := by simp
  have hdn : ((d : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd.ne')
  have key : ∀ k : Fin K, ∑ C : Fin K → Word n d, ∑ k' ∈ Finset.univ.erase k, F (C k) (C k') =
      ((K : ℝ) - 1) * ((d : ℝ) ^ n) ^ K * ((∑ x, ∑ y, F x y) / ((d : ℝ) ^ n) ^ 2) := by
    intro k
    rw [Finset.sum_comm]
    have : ∀ k' ∈ Finset.univ.erase k, ∑ C : Fin K → Word n d, F (C k) (C k') =
        ((d : ℝ) ^ n) ^ K * ((∑ x, ∑ y, F x y) / ((d : ℝ) ^ n) ^ 2) := by
      intro k' hk'
      have hne : k ≠ k' := (Finset.ne_of_mem_erase hk').symm
      rw [pair_marginal hne F, hW]
      have hK : 2 ≤ K := by
        have := Finset.card_le_univ ({k, k'} : Finset (Fin K))
        rw [Finset.card_pair hne, Fintype.card_fin] at this; exact this
      have : ((d : ℝ) ^ n) ^ K = ((d : ℝ) ^ n) ^ (K - 2) * ((d : ℝ) ^ n) ^ 2 := by
        rw [← pow_add]; congr 1; omega
      rw [this]
      field_simp
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · exact absurd k.2 (by omega)
    · push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hK.ne')]; ring
  rw [Finset.sum_congr rfl (fun k _ => key k)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin] at hsum
  have hcard : (Fintype.card (Fin K → Word n d) : ℝ) = ((d : ℝ) ^ n) ^ K := by simp
  rw [hcard] at hsum
  linarith

/-- Markov expurgation: from a size-(2M-1) code with total pair-sum ≤ K(K-1)T, get M indices
whose individual sums are ≤ 2(K-1)T. -/
lemma markov {K M : ℕ} (hK : K = 2 * M - 1) (hM : 0 < M) (Y : Fin K → ℝ) (hY0 : ∀ k, 0 ≤ Y k)
    (T : ℝ) (hT : 0 ≤ T) (hsum : ∑ k, Y k ≤ (K : ℝ) * (K - 1) * T) :
    ∃ e : Fin M ↪ Fin K, ∀ m, Y (e m) ≤ 2 * ((K : ℝ) - 1) * T := by
  have hKR : (K : ℝ) = 2 * M - 1 := by
    rw [hK, Nat.cast_sub (by omega)]; push_cast; ring
  set V : ℝ := 2 * ((K : ℝ) - 1) * T with hV
  set G := Finset.univ.filter (fun k => Y k ≤ V) with hG
  set B := Finset.univ.filter (fun k => ¬ Y k ≤ V) with hB
  have hGB : G.card + B.card = K := by
    rw [hG, hB, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hBc : B.card ≤ M - 1 := by
    by_cases hB0 : B.card = 0
    · omega
    have hne : B.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hB0)
    have h1 : ∑ k ∈ B, V < ∑ k ∈ B, Y k :=
      Finset.sum_lt_sum_of_nonempty hne (fun k hk => lt_of_not_ge (Finset.mem_filter.mp hk).2)
    have h2 : ∑ k ∈ B, Y k ≤ ∑ k, Y k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hY0 k)
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have h3 : (2 * (B.card : ℝ)) * (((K : ℝ) - 1) * T) < (K : ℝ) * (((K : ℝ) - 1) * T) := by
      have e1 : (B.card : ℝ) * V = (2 * (B.card : ℝ)) * (((K : ℝ) - 1) * T) := by rw [hV]; ring
      have e2 : (K : ℝ) * ((K : ℝ) - 1) * T = (K : ℝ) * (((K : ℝ) - 1) * T) := by ring
      linarith
    have hK1 : (1 : ℝ) ≤ K := by rw [hKR]; have : (1 : ℝ) ≤ M := by exact_mod_cast hM
                                 linarith
    have hnn : 0 ≤ ((K : ℝ) - 1) * T := mul_nonneg (by linarith) hT
    have hpos : 0 < ((K : ℝ) - 1) * T := by
      rcases hnn.lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero, mul_zero] at h3; exact absurd h3 (lt_irrefl _)
    have h4 : 2 * (B.card : ℝ) < K := lt_of_mul_lt_mul_right h3 hpos.le
    have h5 : 2 * B.card < K := by exact_mod_cast h4
    omega
  have hGc : M ≤ G.card := by omega
  obtain ⟨G', hG'G, hG'c⟩ := Finset.exists_subset_card_eq hGc
  let e := G'.orderEmbOfFin hG'c
  refine ⟨e.toEmbedding, fun m => ?_⟩
  have : e m ∈ G := hG'G (Finset.orderEmbOfFin_mem G' hG'c m)
  exact (Finset.mem_filter.mp this).2

lemma subsum {K M : ℕ} (e : Fin M ↪ Fin K) (f : Fin K → ℝ) (hf : ∀ k, 0 ≤ f k) (m : Fin M) :
    ∑ m' ∈ Finset.univ.erase m, f (e m') ≤ ∑ k' ∈ Finset.univ.erase (e m), f k' := by
  rw [← Finset.sum_map (Finset.univ.erase m) e f]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k' hk'
    obtain ⟨m', hm', rfl⟩ := Finset.mem_map.mp hk'
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    exact (Finset.ne_of_mem_erase hm') (e.injective h)
  · intro k _ _; exact hf k

noncomputable def Fth (n d : ℕ) (p r : ℝ) (x y : Word n d) : ℝ :=
  ∑ S : Finset (Fin n), (if r ≤ (S.card : ℝ) then patternWeight n p S else 0) *
    (if ∀ i ∈ S, y i = x i then 1 else 0)

lemma pw_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) :
    0 ≤ patternWeight n p S := by
  unfold patternWeight; exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hp0 _)

lemma Fth_nonneg {n d : ℕ} {p r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x y : Word n d) : 0 ≤ Fth n d p r x y :=
  Finset.sum_nonneg fun S _ => mul_nonneg (by split_ifs; exact pw_nonneg hp0 hp1 S; exact le_refl _)
    (by split_ifs <;> norm_num)

lemma err_t {n d M : ℕ} (p r : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (C : Fin M → Word n d) (m : Fin M) :
    1 - deterministicIndividual p C m ≤
      ∑ S : Finset (Fin n), (if (S.card : ℝ) < r then patternWeight n p S else 0) +
      (1 / 2) * ∑ m' ∈ Finset.univ.erase m, Fth n d p r (C m) (C m') := by
  unfold deterministicIndividual
  conv_lhs => rw [← wsum n p]
  rw [← Finset.sum_sub_distrib]
  have hcard : ∀ S : Finset (Fin n), ((compatible C S m).card : ℝ) =
      1 + ∑ m' ∈ Finset.univ.erase m, (if ∀ i ∈ S, C m' i = C m i then 1 else 0) := by
    intro S
    unfold compatible
    rw [Finset.card_filter, Nat.cast_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
    simp
  have hterm : ∀ S : Finset (Fin n), patternWeight n p S - patternWeight n p S /
      ((compatible C S m).card : ℝ) ≤ (if (S.card : ℝ) < r then patternWeight n p S else 0) +
      (1 / 2) * ((if r ≤ (S.card : ℝ) then patternWeight n p S else 0) *
        ∑ m' ∈ Finset.univ.erase m, (if ∀ i ∈ S, C m' i = C m i then 1 else 0)) := by
    intro S
    rw [hcard S]
    set c := ∑ m' ∈ Finset.univ.erase m, (if ∀ i ∈ S, C m' i = C m i then (1 : ℝ) else 0)
    have hcN : c = ((Finset.univ.erase m).filter (fun m' => ∀ i ∈ S, C m' i = C m i)).card := by
      simp only [c]; rw [Finset.sum_boole]
    have hc : 0 ≤ c := by rw [hcN]; positivity
    have hc1 : 0 < 1 + c := by linarith
    have hw := pw_nonneg hp0 hp1 S (n := n)
    rw [div_eq_mul_inv, ← mul_one_sub]
    have hA : 1 - (1 + c)⁻¹ ≤ 1 := by
      have : 0 ≤ (1 + c)⁻¹ := inv_nonneg.mpr hc1.le
      linarith
    have hB : 1 - (1 + c)⁻¹ ≤ (1 / 2) * c := by
      rw [sub_le_iff_le_add, ← sub_le_iff_le_add', inv_eq_one_div, le_div_iff₀ hc1]
      rcases Nat.eq_zero_or_pos ((Finset.univ.erase m).filter (fun m' => ∀ i ∈ S, C m' i = C m i)).card
        with h0 | h0
      · rw [hcN, h0]; norm_num
      · have : (1 : ℝ) ≤ c := by rw [hcN]; exact_mod_cast h0
        nlinarith
    by_cases hr : (S.card : ℝ) < r
    · rw [if_pos hr, if_neg (not_le.mpr hr), zero_mul, mul_zero, add_zero]
      calc patternWeight n p S * (1 - (1 + c)⁻¹) ≤ patternWeight n p S * 1 :=
            mul_le_mul_of_nonneg_left hA hw
        _ = _ := mul_one _
    · rw [if_neg hr, if_pos (not_lt.mp hr), zero_add]
      calc patternWeight n p S * (1 - (1 + c)⁻¹) ≤ patternWeight n p S * ((1 / 2) * c) :=
            mul_le_mul_of_nonneg_left hB hw
        _ = _ := by ring
  refine (Finset.sum_le_sum fun S _ => hterm S).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 2
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

lemma Fth_total {n d : ℕ} (hd : 0 < d) (p r : ℝ) :
    ∑ x : Word n d, ∑ y : Word n d, Fth n d p r x y =
      ((d : ℝ) ^ n) ^ 2 * ∑ S : Finset (Fin n),
        (if r ≤ (S.card : ℝ) then patternWeight n p S else 0) * ((d : ℝ) ^ S.card)⁻¹ := by
  unfold Fth
  have hsw : ∀ x : Word n d, ∑ y : Word n d, ∑ S : Finset (Fin n),
      (if r ≤ (S.card : ℝ) then patternWeight n p S else 0) * (if ∀ i ∈ S, y i = x i then 1 else 0) =
      ∑ S : Finset (Fin n), ∑ y : Word n d,
      (if r ≤ (S.card : ℝ) then patternWeight n p S else 0) * (if ∀ i ∈ S, y i = x i then 1 else 0) :=
    fun x => Finset.sum_comm
  simp_rw [hsw]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp_rw [← Finset.mul_sum]
  have hcount : ∑ x : Word n d, ∑ y : Word n d, (if ∀ i ∈ S, y i = x i then (1 : ℝ) else 0) =
      ((d : ℝ) ^ n) ^ 2 * ((d : ℝ) ^ S.card)⁻¹ := by
    have hI : ∀ x y : Word n d, (if ∀ i ∈ S, y i = x i then (1 : ℝ) else 0) =
        ∏ i, (if i ∈ S then (if y i = x i then 1 else 0) else 1) := by
      intro x y
      by_cases h : ∀ i ∈ S, y i = x i
      · rw [if_pos h]; symm
        apply Finset.prod_eq_one
        intro i _
        split_ifs with h1 h2 <;> first | rfl | exact absurd (h i h1) h2
      · rw [if_neg h]; symm
        push Not at h
        obtain ⟨i, hi, hne⟩ := h
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi, hne]
    simp_rw [hI]
    rw [prod_total (fun i a c => if i ∈ S then (if c = a then (1 : ℝ) else 0) else 1)]
    have hrow : ∀ i : Fin n, ∑ a : Fin d, ∑ c : Fin d,
        (if i ∈ S then (if c = a then (1 : ℝ) else 0) else 1) =
        if i ∈ S then (d : ℝ) else (d : ℝ) * d := by
      intro i
      split_ifs
      · simp
      · simp
    simp_rw [hrow]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have h1 : (Finset.univ.filter (fun i : Fin n => i ∈ S)) = S := by ext; simp
    have h2 : (Finset.univ.filter (fun i : Fin n => i ∉ S)).card = n - S.card := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin n => i ∈ S)
      rw [h1, Finset.card_univ, Fintype.card_fin] at this; omega
    rw [h1, h2]
    have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [show ((d : ℝ)) ^ n = (d : ℝ) ^ S.card * (d : ℝ) ^ (n - S.card) by
      rw [← pow_add]; congr 1; omega]
    field_simp
    ring
  rw [hcount]; ring

lemma A_eq (n : ℕ) (p r : ℝ) :
    ∑ S : Finset (Fin n), (if (S.card : ℝ) < r then patternWeight n p S else 0) =
      ∑ k ∈ (Finset.range (n+1)).filter (fun k : ℕ => (k : ℝ) < r), binomialWeight n p k := by
  have : ∀ S : Finset (Fin n), (if (S.card : ℝ) < r then patternWeight n p S else 0) =
      (fun k : ℕ => if (k : ℝ) < r then (1 - p) ^ k * p ^ (n - k) else 0) S.card := fun S => rfl
  rw [Finset.sum_congr rfl (fun S _ => this S), ← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun k : ℕ => if (k : ℝ) < r then (1 - p) ^ k * p ^ (n - k) else 0),
    Finset.card_univ, Fintype.card_fin, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold binomialWeight
  split_ifs <;> simp [nsmul_eq_mul]; ring

lemma B_eq (n d : ℕ) (p r : ℝ) :
    ∑ S : Finset (Fin n), (if r ≤ (S.card : ℝ) then patternWeight n p S else 0) * ((d : ℝ) ^ S.card)⁻¹ =
      ∑ k ∈ (Finset.range (n+1)).filter (fun k : ℕ => r ≤ (k : ℝ)),
        binomialWeight n p k * ((d : ℝ) ^ k)⁻¹ := by
  have : ∀ S : Finset (Fin n), (if r ≤ (S.card : ℝ) then patternWeight n p S else 0) * ((d : ℝ) ^ S.card)⁻¹ =
      (fun k : ℕ => if r ≤ (k : ℝ) then (1 - p) ^ k * p ^ (n - k) * ((d : ℝ) ^ k)⁻¹ else 0) S.card := by
    intro S; simp only; split_ifs <;> simp [patternWeight]
  rw [Finset.sum_congr rfl (fun S _ => this S), ← Finset.powerset_univ,
    Finset.sum_powerset_apply_card
      (fun k : ℕ => if r ≤ (k : ℝ) then (1 - p) ^ k * p ^ (n - k) * ((d : ℝ) ^ k)⁻¹ else 0),
    Finset.card_univ, Fintype.card_fin, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold binomialWeight
  split_ifs <;> simp [nsmul_eq_mul]; ring

end G54E

open QAlgorithms.Papers.Independent.Information100.P58

theorem solution (n d M : ℕ) (hn : 0<n) (hd : 2≤d) (hM : 0<M)
    (p r : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    ∃ C : Fin M → Word n d, ∀ m,
      1-deterministicIndividual p C m ≤ thresholdBound n d M p r := by
  have hd0 : 0 < d := by omega
  set K : ℕ := 2 * M - 1 with hK
  have hKR : (K : ℝ) = 2 * M - 1 := by
    rw [hK, Nat.cast_sub (by omega)]; push_cast; ring
  set B' := ∑ S : Finset (Fin n), (if r ≤ (S.card : ℝ) then patternWeight n p S else 0) *
    ((d : ℝ) ^ S.card)⁻¹ with hB'
  have hB0 : 0 ≤ B' := Finset.sum_nonneg fun S _ => mul_nonneg
    (by split_ifs; exact G54E.pw_nonneg hp0 hp1 S; exact le_refl _) (by positivity)
  obtain ⟨C0, hC0⟩ := G54E.avg_gen (K := K) (n := n) hd0 (G54E.Fth n d p r)
  rw [G54E.Fth_total hd0, ← hB', mul_div_cancel_left₀ _ (pow_ne_zero _ (pow_ne_zero _
    (by exact_mod_cast hd0.ne')))] at hC0
  set Y : Fin K → ℝ := fun k => ∑ k' ∈ Finset.univ.erase k, G54E.Fth n d p r (C0 k) (C0 k') with hY
  have hY0 : ∀ k, 0 ≤ Y k := fun k => Finset.sum_nonneg fun _ _ => G54E.Fth_nonneg hp0 hp1 _ _
  obtain ⟨e, he⟩ := G54E.markov hK hM Y hY0 B' hB0 hC0
  refine ⟨fun m => C0 (e m), fun m => ?_⟩
  unfold thresholdBound
  apply le_min
  · have : 0 ≤ deterministicIndividual p (fun m => C0 (e m)) m := by
      unfold deterministicIndividual
      exact Finset.sum_nonneg fun S _ => div_nonneg (G54E.pw_nonneg hp0 hp1 S) (Nat.cast_nonneg _)
    linarith
  · have h1 := G54E.err_t p r hp0 hp1 (fun m => C0 (e m)) m
    have h2 := G54E.subsum e (fun k' => G54E.Fth n d p r (C0 (e m)) (C0 k'))
      (fun _ => G54E.Fth_nonneg hp0 hp1 _ _) m
    have h3 := he m
    rw [G54E.A_eq] at h1
    rw [← G54E.B_eq, ← hB']
    have h4 : (1 / 2 : ℝ) * Y (e m) ≤ ((K : ℝ) - 1) * B' := by linarith
    have h5 : ((K : ℝ) - 1) * B' ≤ (2 * (M : ℝ) - 1) * B' := by
      apply mul_le_mul_of_nonneg_right _ hB0; rw [hKR]; linarith
    simp only [Y] at h4
    linarith
