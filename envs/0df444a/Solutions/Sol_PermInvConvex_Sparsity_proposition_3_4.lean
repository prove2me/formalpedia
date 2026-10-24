-- Prove2me | solution 1 for PermInvConvex.Sparsity.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:25:07.096367+00:00
-- url     : https://prove2.me/submissions/2142778c-e66e-4f3d-b0f3-c0e015cba1d0

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Definitions.Def_PermInvConvex_Sparsity_Majorization
import Definitions.Def_PermInvConvex_Sparsity_Setting

open ModernConvex.Spectral
open Set

namespace PermInvConvex.Sparsity

/- The elementary top-sum lemmas below are adapted from the accepted proof of
ModernConvex.Spectral.majorization_principle supplied in the majorized-norm
source packet. Their complete proofs are included here; no theorem import or
external axiom is used. -/

lemma rec_card_R {m : ℕ} (j : ℕ) (hj : j ≤ m) :
    (Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).card = j := by
  rw [Fin.card_filter_val_lt]; omega

lemma rec_top {m : ℕ} (c : Fin m → ℝ) (hc : Antitone c) (s : Finset (Fin m)) (j : ℕ)
    (hs : s.card = j) :
    ∑ i ∈ s, c i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), c i := by
  set R := Finset.univ.filter (fun i : Fin m => (i : ℕ) < j) with hR
  have hjm : j ≤ m := by rw [← hs]; simpa using Finset.card_le_univ s
  have hRc : R.card = j := rec_card_R j hjm
  have hcard : (s \ R).card = (R \ s).card := by
    have h1 := Finset.card_sdiff_add_card_inter s R
    have h2 := Finset.card_sdiff_add_card_inter R s
    rw [Finset.inter_comm] at h2
    omega
  have hpq : ∀ p ∈ s \ R, ∀ q ∈ R \ s, c p ≤ c q := by
    intro p hp q hq
    simp only [Finset.mem_sdiff, hR, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact hc (Fin.le_iff_val_le_val.mpr (by omega))
  have hdiff : ∑ i ∈ s \ R, c i ≤ ∑ i ∈ R \ s, c i := by
    rcases (s \ R).eq_empty_or_nonempty with he | hne
    · have : R \ s = ∅ := by
        rw [← Finset.card_eq_zero, ← hcard, he, Finset.card_empty]
      rw [he, this]
    · obtain ⟨p0, hp0, hmax⟩ := Finset.exists_max_image (s \ R) c hne
      calc ∑ i ∈ s \ R, c i ≤ (s \ R).card • c p0 := Finset.sum_le_card_nsmul _ _ _ hmax
        _ = (R \ s).card • c p0 := by rw [hcard]
        _ ≤ ∑ i ∈ R \ s, c i := Finset.card_nsmul_le_sum _ _ _ (fun q hq => hpq p0 hp0 q hq)
  rw [← Finset.sum_inter_add_sum_sdiff s R, ← Finset.sum_inter_add_sum_sdiff R s,
    Finset.inter_comm]
  linarith

lemma rec_le_sumLargest {m : ℕ} (y : Fin m → ℝ) (s : Finset (Fin m)) (j : ℕ) (hs : s.card = j) :
    ∑ i ∈ s, y i ≤ sumLargest j y := by
  unfold sumLargest
  exact le_ciSup (f := fun s : {s : Finset (Fin m) // s.card = j} => ∑ i ∈ s.1, y i)
    (Set.finite_range _).bddAbove ⟨s, hs⟩

lemma rec_sumLargest_le {m : ℕ} (x : Fin m → ℝ) (π : Equiv.Perm (Fin m)) (hπ : Antitone (x ∘ π))
    (j : ℕ) (hj : j ≤ m) :
    sumLargest j x ≤ ∑ k ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), x (π k) := by
  unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, rec_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  have hc : (s.1.map π.symm.toEmbedding).card = j := by rw [Finset.card_map]; exact s.2
  have := rec_top (x ∘ π) hπ _ j hc
  simpa [Finset.sum_map] using this


lemma rec_dec_antitone {n : ℕ} (x : Fin n → ℝ) : Antitone (decAbs x) := by
  intro i j hij
  exact Tuple.monotone_sort (absVec x) (Fin.rev_le_rev.mpr hij)

lemma rec_dec_nonneg {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : 0 ≤ decAbs x i :=
  abs_nonneg _

noncomputable def rec_tail {n : ℕ} (a : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ) + 1), a j

lemma rec_tail_step {n : ℕ} (a : Fin n → ℝ) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    rec_tail a i = a ⟨i - 1, by omega⟩ + rec_tail a (i + 1) := by
  classical
  have heq : Finset.univ.filter (fun j : Fin n => i ≤ (j : ℕ) + 1) =
      insert ⟨i - 1, by omega⟩ (Finset.univ.filter (fun j : Fin n => i + 1 ≤ (j : ℕ) + 1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]
    omega
  have hnot : (⟨i - 1, by omega⟩ : Fin n) ∉
      Finset.univ.filter (fun j : Fin n => i + 1 ≤ (j : ℕ) + 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  unfold rec_tail
  rw [heq, Finset.sum_insert hnot]

lemma rec_sval {n : ℕ} (K : ℕ) (hKn : K < n) (x : Fin n → ℝ)
    (i : ℕ) (hi : 1 ≤ i) (hiK : i ≤ K - 1) :
    sVal K x (i + 1) - sVal K x i =
      1 / ((K : ℝ) - i + 1) * (sVal K x (i + 1) - decAbs x ⟨i - 1, by omega⟩) ∧
    sVal K x (i + 1) - sVal K x i =
      1 / ((K : ℝ) - i) * (sVal K x i - decAbs x ⟨i - 1, by omega⟩) := by
  have hik : (i : ℝ) < K := by exact_mod_cast (show i < K by omega)
  have hd : (K : ℝ) - i ≠ 0 := by linarith
  have hd' : (K : ℝ) - i + 1 ≠ 0 := by linarith
  have hs : rec_tail (decAbs x) i =
      decAbs x ⟨i - 1, by omega⟩ + rec_tail (decAbs x) (i + 1) :=
    rec_tail_step (decAbs x) i hi (by omega)
  simp only [sVal, Nat.cast_add, Nat.cast_one]
  change rec_tail (decAbs x) (i + 1) / ((K : ℝ) - (i + 1) + 1) -
      rec_tail (decAbs x) i / ((K : ℝ) - i + 1) =
      1 / ((K : ℝ) - i + 1) *
        (rec_tail (decAbs x) (i + 1) / ((K : ℝ) - (i + 1) + 1) - decAbs x ⟨i - 1, by omega⟩) ∧
    rec_tail (decAbs x) (i + 1) / ((K : ℝ) - (i + 1) + 1) -
      rec_tail (decAbs x) i / ((K : ℝ) - i + 1) =
      1 / ((K : ℝ) - i) *
        (rec_tail (decAbs x) i / ((K : ℝ) - i + 1) - decAbs x ⟨i - 1, by omega⟩)
  rw [hs]
  have hdform : (K : ℝ) - (i + 1) + 1 = K - i := by ring
  rw [hdform]
  constructor <;> field_simp [hd, hd'] <;> ring

lemma rec_ix {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (x : Fin n → ℝ) :
    1 ≤ ix K x ∧ ix K x ≤ K ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ K → sVal K x (ix K x) ≤ sVal K x i := by
  have hne : {i : ℕ | 1 ≤ i ∧ i ≤ K ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ K → sVal K x i ≤ sVal K x j}.Nonempty := by
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 K) (sVal K x)
      ⟨1, by simp [hK]⟩
    refine ⟨i, (Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2, ?_⟩
    intro j hj hjK
    exact hmin j (Finset.mem_Icc.mpr ⟨hj, hjK⟩)
  exact csInf_mem hne

lemma rec_increase_step {n : ℕ} (K : ℕ) (hKn : K < n) (x : Fin n → ℝ)
    (i : ℕ) (hi : 1 ≤ i) (hiK : i + 1 < K)
    (hinc : sVal K x i ≤ sVal K x (i + 1)) :
    sVal K x (i + 1) ≤ sVal K x (i + 2) := by
  have hr := rec_sval K hKn x i hi (by omega)
  have hr' := rec_sval K hKn x (i + 1) (by omega) (by omega)
  have hden : 0 < (K : ℝ) - i + 1 := by
    have : (i : ℝ) < K := by exact_mod_cast (show i < K by omega)
    linarith
  have ha : decAbs x ⟨i - 1, by omega⟩ ≤ sVal K x (i + 1) := by
    have hprod : 0 ≤ 1 / ((K : ℝ) - i + 1) *
        (sVal K x (i + 1) - decAbs x ⟨i - 1, by omega⟩) := by
      rw [← hr.1]
      exact sub_nonneg.mpr hinc
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (one_div_pos.mpr hden)).mp hprod)
  have ha' : decAbs x ⟨i + 1 - 1, by omega⟩ ≤ sVal K x (i + 1) :=
    (rec_dec_antitone x (show (⟨i - 1, by omega⟩ : Fin n) ≤ ⟨i + 1 - 1, by omega⟩ by
      simp only [Fin.le_iff_val_le_val]; omega)).trans ha
  apply sub_nonneg.mp
  rw [show i + 2 = i + 1 + 1 by omega, hr'.2]
  apply mul_nonneg
  · apply le_of_lt
    apply one_div_pos.mpr
    apply sub_pos.mpr
    exact_mod_cast hiK
  · exact sub_nonneg.mpr ha'

lemma rec_upward {n : ℕ} (K : ℕ) (hKn : K < n) (x : Fin n → ℝ)
    (i : ℕ) (hi : 1 ≤ i) (_hiK : i < K)
    (hinc : sVal K x i ≤ sVal K x (i + 1)) :
    MonotoneOn (sVal K x) (Set.Icc i K) := by
  have hstep : ∀ j, i ≤ j → j < K → sVal K x j ≤ sVal K x (j + 1) := by
    intro j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ => hinc
    | succ j hij ih =>
      intro hjK
      exact rec_increase_step K hKn x j (by omega) hjK (ih (by omega))
  apply monotoneOn_of_le_add_one Set.ordConnected_Icc
  intro j _ hj hj'
  exact hstep j hj.1 (by have := hj'.2; omega)

lemma rec_unimodal {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (hKn : K < n) (x : Fin n → ℝ) :
    (∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ ix K x → sVal K x j ≤ sVal K x i) ∧
    (∀ i j : ℕ, ix K x ≤ i → i ≤ j → j ≤ K → sVal K x i ≤ sVal K x j) := by
  obtain ⟨hm1, hmK, hmin⟩ := rec_ix K hK x
  constructor
  · have hanti : AntitoneOn (sVal K x) (Set.Icc 1 (ix K x)) := by
      apply antitoneOn_of_add_one_le Set.ordConnected_Icc
      intro i _ hi hi'
      have hii : 1 ≤ i := hi.1
      have hii' : i + 1 ≤ ix K x := hi'.2
      by_contra hn
      have hlt : sVal K x i < sVal K x (i + 1) := lt_of_not_ge hn
      have hup := rec_upward K hKn x i hi.1 (by have := hi'.2; omega) hlt.le
      have hle := hup (show i + 1 ∈ Set.Icc i K by constructor <;> omega)
        (show ix K x ∈ Set.Icc i K by constructor <;> omega) hi'.2
      have hmin' := hmin i hi.1 (by have := hi.2; omega)
      linarith
    intro i j hi hij hj
    exact hanti ⟨hi, by omega⟩ ⟨by omega, hj⟩ hij
  · intro i j hi hij hj
    by_cases hm : ix K x < K
    · have hup := rec_upward K hKn x (ix K x) hm1 hm
        (hmin (ix K x + 1) (by omega) (by omega))
      exact hup ⟨hi, by omega⟩ ⟨by omega, hj⟩ hij
    · have heq : i = j := by omega
      rw [heq]

lemma rec_delta_tail {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (hKn : K < n) (x : Fin n → ℝ)
    (j : Fin n) (hj : ix K x ≤ (j : ℕ) + 1) : decAbs x j ≤ delta K x := by
  obtain ⟨hm1, hmK, hmin⟩ := rec_ix K hK x
  have hbase : decAbs x ⟨ix K x - 1, by omega⟩ ≤ sVal K x (ix K x) := by
    by_cases hm : ix K x < K
    · have hr := (rec_sval K hKn x (ix K x) hm1 (by omega)).2
      have hinc := hmin (ix K x + 1) (by omega) (by omega)
      have hd : 0 < 1 / ((K : ℝ) - ix K x) := by
        apply one_div_pos.mpr
        apply sub_pos.mpr
        exact_mod_cast hm
      have hp : 0 ≤ 1 / ((K : ℝ) - ix K x) *
          (sVal K x (ix K x) - decAbs x ⟨ix K x - 1, by omega⟩) := by
        rw [← hr]
        exact sub_nonneg.mpr hinc
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hd).mp hp)
    · have hm : ix K x = K := by omega
      simp only [hm, sVal, sub_self, zero_add, div_one]
      apply Finset.single_le_sum (fun i _ => rec_dec_nonneg x i)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  exact (rec_dec_antitone x (show (⟨ix K x - 1, by omega⟩ : Fin n) ≤ j by
    simp only [Fin.le_iff_val_le_val]; omega)).trans hbase

lemma rec_delta_nonneg {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (hKn : K < n) (x : Fin n → ℝ) :
    0 ≤ delta K x := by
  obtain ⟨hm1, hmK, _⟩ := rec_ix K hK x
  exact (rec_dec_nonneg x ⟨ix K x - 1, by omega⟩).trans
    (rec_delta_tail K hK hKn x ⟨ix K x - 1, by omega⟩ (by simp; omega))

lemma rec_delta_head {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (hKn : K < n) (x : Fin n → ℝ)
    (j : Fin n) (hj : (j : ℕ) + 1 < ix K x) : delta K x ≤ decAbs x j := by
  obtain ⟨hm1, hmK, hmin⟩ := rec_ix K hK x
  have hr := (rec_sval K hKn x ((j : ℕ) + 1) (by omega) (by omega)).1
  have hdec := (rec_unimodal K hK hKn x).1 ((j : ℕ) + 1) ((j : ℕ) + 1 + 1)
    (by omega) (by omega) (by omega)
  have hd : 0 < 1 / ((K : ℝ) - ((j : ℕ) + 1) + 1) := by
    apply one_div_pos.mpr
    have hcast : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast (show (j : ℕ) + 1 ≤ K by omega)
    push_cast at hcast
    linarith
  have hp : 1 / ((K : ℝ) - ((j : ℕ) + 1) + 1) *
      (sVal K x ((j : ℕ) + 1 + 1) - decAbs x j) ≤ 0 := by
    simpa only [Nat.add_sub_cancel, Fin.eta, Nat.cast_add, Nat.cast_one] using hr.symm.trans_le (sub_nonpos.mpr hdec)
  exact (hmin ((j : ℕ) + 1 + 1) (by omega) (by omega)).trans
    (by nlinarith)

lemma rec_u_dominates {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (hKn : K < n) (x : Fin n → ℝ)
    (j : Fin n) (hj : (j : ℕ) < K) : decAbs x j ≤ uVec K x j := by
  unfold uVec
  split_ifs with h
  · exact le_rfl
  · exact rec_delta_tail K hK hKn x j (by omega)
  · omega

lemma rec_u_nonneg {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (hKn : K < n) (x : Fin n → ℝ)
    (j : Fin n) : 0 ≤ uVec K x j := by
  unfold uVec
  split_ifs
  · exact rec_dec_nonneg x j
  · exact rec_delta_nonneg K hK hKn x
  · exact le_rfl

lemma rec_u_antitone {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (hKn : K < n) (x : Fin n → ℝ) :
    Antitone (uVec K x) := by
  obtain ⟨hm1, hmK, _⟩ := rec_ix K hK x
  intro i j hij
  have hij' : (i : ℕ) ≤ (j : ℕ) := hij
  unfold uVec
  split_ifs with hjm hjK him hiK
  all_goals first
  | exact rec_dec_antitone x hij
  | exact rec_delta_head K hK hKn x i (by omega)
  | exact rec_dec_nonneg x i
  | exact rec_delta_nonneg K hK hKn x
  | exact le_rfl
  | omega

lemma rec_sum_dec {n : ℕ} (x : Fin n → ℝ) : ∑ i, decAbs x i = ∑ i, absVec x i := by
  exact Equiv.sum_comp (Fin.revPerm.trans (Tuple.sort (absVec x))) (absVec x)

lemma rec_u_total {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (hKn : K < n) (x : Fin n → ℝ) :
    ∑ i, uVec K x i = ∑ i, absVec x i := by
  classical
  obtain ⟨hm1, hmK, hmin⟩ := rec_ix K hK x
  let m := ix K x
  have hmn : m ≤ n := by dsimp [m]; omega
  have hcard : (Finset.univ.filter (fun j : Fin n =>
      ¬((j : ℕ) + 1 < m) ∧ (j : ℕ) + 1 ≤ K)).card = K - (m - 1) := by
    have heq : Finset.univ.filter (fun j : Fin n =>
        ¬((j : ℕ) + 1 < m) ∧ (j : ℕ) + 1 ≤ K) =
        Finset.univ.filter (fun j : Fin n => (j : ℕ) < K) \
          Finset.univ.filter (fun j : Fin n => (j : ℕ) < m - 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      omega
    rw [heq, Finset.card_sdiff_of_subset, rec_card_R K (by omega), rec_card_R (m - 1) (by omega)]
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    dsimp [m] at hj
    omega
  have hcast : ((K - (m - 1) : ℕ) : ℝ) = (K : ℝ) - m + 1 := by
    rw [Nat.cast_sub (by dsimp [m]; omega), Nat.cast_sub (by dsimp [m]; omega)]
    norm_num
    ring
  have hd : (K : ℝ) - m + 1 ≠ 0 := by
    have hmcast : (m : ℝ) ≤ K := by exact_mod_cast hmK
    linarith
  have hprod : ((K : ℝ) - m + 1) * delta K x = rec_tail (decAbs x) m := by
    change ((K : ℝ) - m + 1) * (rec_tail (decAbs x) m / ((K : ℝ) - m + 1)) = _
    exact mul_div_cancel₀ _ hd
  have hsplit : (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) + 1 < m), decAbs x j) +
      rec_tail (decAbs x) m = ∑ j, decAbs x j := by
    simpa only [not_lt, rec_tail] using Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun j : Fin n => (j : ℕ) + 1 < m) (decAbs x)
  rw [← rec_sum_dec x]
  unfold uVec
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter,
    Finset.sum_const, nsmul_eq_mul]
  change (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) + 1 < m), decAbs x j) +
      ((Finset.univ.filter (fun j : Fin n =>
        ¬((j : ℕ) + 1 < m) ∧ (j : ℕ) + 1 ≤ K)).card : ℝ) * delta K x = _
  rw [hcard, hcast, hprod]
  exact hsplit

lemma rec_u_support {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (x : Fin n → ℝ)
    (i : Fin n) (hi : K ≤ (i : ℕ)) : uVec K x i = 0 := by
  have hmK := (rec_ix K hK x).2.1
  simp [uVec, show ¬ ((i : ℕ) + 1 < ix K x) by omega,
    show ¬ ((i : ℕ) + 1 ≤ K) by omega]

lemma rec_majorizes {n : ℕ} (K : ℕ) (hK : 1 ≤ K) (hKn : K < n) (x : Fin n → ℝ) :
    Majorizes (uVec K x) (absVec x) := by
  classical
  constructor
  · intro j hj1 hjn
    have hjn' : j ≤ n := by omega
    calc
      sumLargest j (absVec x) ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), decAbs x i :=
        rec_sumLargest_le (absVec x) (Fin.revPerm.trans (Tuple.sort (absVec x)))
          (rec_dec_antitone x) j hjn'
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), uVec K x i := by
        by_cases hjK : j ≤ K
        · apply Finset.sum_le_sum
          intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          exact rec_u_dominates K hK hKn x i (by omega)
        · have heq : (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), uVec K x i) =
              ∑ i, uVec K x i := by
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro i hi hnot
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
            exact rec_u_support K hK x i (by omega)
          rw [heq, rec_u_total K hK hKn x, ← rec_sum_dec x]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun i _ _ => rec_dec_nonneg x i)
      _ ≤ sumLargest j (uVec K x) := rec_le_sumLargest _ _ j (rec_card_R j hjn')
  · exact (rec_u_total K hK hKn x).symm

lemma rec_first {n : ℕ} (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) :
    uVec K x ⟨0, by omega⟩ = max (decAbs x ⟨0, by omega⟩) (sVal K x 1) := by
  obtain ⟨hm1, hmK, hmin⟩ := rec_ix K hK.le x
  by_cases hm : ix K x = 1
  · have hb := rec_delta_tail K hK.le hKn x ⟨0, by omega⟩ (by simp [hm])
    have hd : delta K x = sVal K x 1 := by simp [delta, hm]
    rw [hd] at hb
    simp [uVec, hm, hd, max_eq_right hb, show 1 ≤ K by omega]
  · have hm' : 1 < ix K x := by omega
    have hdec := (rec_unimodal K hK.le hKn x).1 1 2 (by omega) (by omega) (by omega)
    have hr := (rec_sval K hKn x 1 (by omega) (by omega)).2
    norm_num at hr
    have hd : 0 < 1 / ((K : ℝ) - 1) := by
      apply one_div_pos.mpr
      have : (1 : ℝ) < K := by exact_mod_cast hK
      linarith
    simp only [one_div] at hd
    have hb : sVal K x 1 ≤ decAbs x ⟨0, by omega⟩ := by nlinarith
    simp [uVec, hm', max_eq_left hb]

end PermInvConvex.Sparsity

open PermInvConvex.Sparsity

theorem solution {n : ℕ} (K : ℕ) (hK : 1 < K) (hKn : K < n) (x : Fin n → ℝ) :
    (∀ (i : ℕ) (hi : 1 ≤ i) (hiK : i ≤ K - 1),
        sVal K x (i + 1) - sVal K x i =
            1 / ((K : ℝ) - i + 1) * (sVal K x (i + 1) - decAbs x ⟨i - 1, by omega⟩) ∧
          sVal K x (i + 1) - sVal K x i =
            1 / ((K : ℝ) - i) * (sVal K x i - decAbs x ⟨i - 1, by omega⟩)) ∧
    ((∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ ix K x → sVal K x j ≤ sVal K x i) ∧
      (∀ i j : ℕ, ix K x ≤ i → i ≤ j → j ≤ K → sVal K x i ≤ sVal K x j)) ∧
    Majorizes (uVec K x) (absVec x) ∧
    uVec K x ⟨0, by omega⟩ = max (decAbs x ⟨0, by omega⟩) (sVal K x 1) := by
  exact ⟨rec_sval K hKn x, rec_unimodal K hK.le hKn x,
    rec_majorizes K hK.le hKn x, rec_first K hK hKn x⟩
