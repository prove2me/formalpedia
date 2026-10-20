-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P58.finiteExpurgatedBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:31:01.805858+00:00
-- url     : https://prove2.me/submissions/d6476d0e-8006-4f3f-b7cd-f0e99339b69c

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

end G54E

open QAlgorithms.Papers.Independent.Information100.P58

theorem solution (n d M : ℕ) (hn : 0<n) (hd : 2≤d) (hM : 0<M)
    (p s : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (hs : 1 ≤ s) :
    ∃ C : Fin M → Word n d, ∀ m,
      1-deterministicIndividual p C m ≤ expurgatedBound n d M p s := by
  have hd0 : 0 < d := by omega
  set β : ℝ := p ^ (1 / s) with hβ
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hp0 _
  set q : ℝ := 1 / d + (1 - 1 / d) * β with hq
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : 0 ≤ q := by
    have : 0 ≤ 1 - 1 / (d : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    positivity
  set K : ℕ := 2 * M - 1 with hK
  have hKR : (K : ℝ) = 2 * M - 1 := by
    rw [hK, Nat.cast_sub (by omega)]; push_cast; ring
  obtain ⟨C0, hC0⟩ := G54E.avg_code (K := K) (n := n) hd0 β
  set Y : Fin K → ℝ := fun k => ∑ k' ∈ Finset.univ.erase k, β ^ (n - (G54E.agr (C0 k) (C0 k')).card)
    with hY
  have hY0 : ∀ k, 0 ≤ Y k := fun k => Finset.sum_nonneg fun _ _ => pow_nonneg hβ0 _
  set V : ℝ := 2 * ((K : ℝ) - 1) * q ^ n with hV
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
    have h3 : (B.card : ℝ) * (2 * ((K : ℝ) - 1) * q ^ n) < (K : ℝ) * ((K : ℝ) - 1) * q ^ n := by
      have := hC0; simp only [Y] at h2; linarith
    have hpos : 0 < ((K : ℝ) - 1) * q ^ n := by
      by_contra hle
      push Not at hle
      have : 0 ≤ ((K : ℝ) - 1) * q ^ n := by
        have : (1 : ℝ) ≤ K := by rw [hKR]; have : (1 : ℝ) ≤ M := by exact_mod_cast hM
                                 linarith
        exact mul_nonneg (by linarith) (pow_nonneg hq0 _)
      have h0 : ((K : ℝ) - 1) * q ^ n = 0 := le_antisymm hle this
      have : (B.card : ℝ) * (2 * ((K : ℝ) - 1) * q ^ n) = 0 := by
        rw [show (B.card : ℝ) * (2 * ((K : ℝ) - 1) * q ^ n) = 2 * B.card * (((K : ℝ) - 1) * q ^ n) by ring,
          h0, mul_zero]
      rw [this, show (K : ℝ) * ((K : ℝ) - 1) * q ^ n = K * (((K : ℝ) - 1) * q ^ n) by ring, h0,
        mul_zero] at h3
      exact lt_irrefl _ h3
    have h4 : 2 * (B.card : ℝ) < K := by
      have : (B.card : ℝ) * (2 * ((K : ℝ) - 1) * q ^ n) = (2 * B.card) * (((K : ℝ) - 1) * q ^ n) := by ring
      rw [this, show (K : ℝ) * ((K : ℝ) - 1) * q ^ n = K * (((K : ℝ) - 1) * q ^ n) by ring] at h3
      exact lt_of_mul_lt_mul_right h3 hpos.le
    have h5 : 2 * B.card < K := by exact_mod_cast h4
    omega
  have hGc : M ≤ G.card := by omega
  obtain ⟨G', hG'G, hG'c⟩ := Finset.exists_subset_card_eq hGc
  let e := G'.orderEmbOfFin hG'c
  refine ⟨fun m => C0 (e m), fun m => ?_⟩
  have hb := G54E.err_bound p hp0 hp1 (fun m => C0 (e m)) m
  refine hb.trans ?_
  have hpk : ∀ k : ℕ, p ^ k = (β ^ k) ^ s := by
    intro k
    have hbs : β ^ s = p := by
      rw [hβ, ← Real.rpow_mul hp0, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
    rw [← Real.rpow_natCast β k, ← Real.rpow_mul hβ0, mul_comm, Real.rpow_mul hβ0, Real.rpow_natCast, hbs]
  simp_rw [hpk]
  have hs1 := G54E.sum_rpow_le (Finset.univ.erase m)
    (fun m' => β ^ (n - (G54E.agr (C0 (e m)) (C0 (e m'))).card)) (fun _ => pow_nonneg hβ0 _) hs
  refine (mul_le_mul_of_nonneg_left hs1 (by norm_num)).trans ?_
  unfold expurgatedBound
  rw [← hβ, ← hq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => pow_nonneg hβ0 _) _ (by linarith)
  -- sub-sum ≤ Y (e m) ≤ V ≤ 2(2M-1)q^n
  have hsub : ∑ m' ∈ Finset.univ.erase m, β ^ (n - (G54E.agr (C0 (e m)) (C0 (e m'))).card) ≤ Y (e m) := by
    have : ∑ m' ∈ Finset.univ.erase m, β ^ (n - (G54E.agr (C0 (e m)) (C0 (e m'))).card) =
        ∑ k' ∈ (Finset.univ.erase m).map e.toEmbedding, β ^ (n - (G54E.agr (C0 (e m)) (C0 k')).card) := by
      rw [Finset.sum_map]; rfl
    rw [this]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k' hk'
      obtain ⟨m', hm', rfl⟩ := Finset.mem_map.mp hk'
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      exact (Finset.ne_of_mem_erase hm') (e.injective h)
    · intro _ _ _; exact pow_nonneg hβ0 _
  have hYV : Y (e m) ≤ V := by
    have : e m ∈ G := hG'G (Finset.orderEmbOfFin_mem G' hG'c m)
    exact (Finset.mem_filter.mp this).2
  have hV2 : V ≤ 2 * (2 * (M : ℝ) - 1) * q ^ n := by
    rw [hV, hKR]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq0 _)
    linarith
  linarith
