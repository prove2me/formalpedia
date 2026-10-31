-- Prove2me | solution 1 for RobustPrefLearn.MTP.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:22:23.63699+00:00
-- url     : https://prove2.me/submissions/8a2e174a-4537-4294-9f43-fc0f33264c29

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA
import Theorems.Thm_RobustPrefLearn_MTP_lemma_4
import Theorems.Thm_RobustPrefLearn_MTP_lemma_5
import Theorems.Thm_RobustPrefLearn_MTP_lemma_6

open scoped ENNReal

namespace MTPAux7
open RobustPrefLearn.MTP

lemma sum_rank {K : ℕ} (g : ℕ → ℝ) (T : Finset (Fin K)) :
    ∑ X ∈ T, g (T.filter (fun k => k ≤ X)).card = ∑ j ∈ Finset.range T.card, g (j + 1) := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a T ha ih =>
    have haT : a ∉ T := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert haT, Finset.card_insert_of_notMem haT, Finset.sum_range_succ]
    have h1 : (insert a T).filter (fun k => k ≤ a) = insert a T := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · exact (ha x hx).le
    have h2 : ∀ X ∈ T, (insert a T).filter (fun k => k ≤ X) = T.filter (fun k => k ≤ X) := by
      intro X hX
      rw [Finset.filter_insert, if_neg (not_le.2 (ha X hX))]
    rw [h1, Finset.card_insert_of_notMem haT, Finset.sum_congr rfl (fun X hX => by rw [h2 X hX]),
      ih]
    ring

lemma g_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) :
    0 < 1 - ((m + 2 : ℕ) : ℝ) * p ^ (m + 1) + (((m + 2 : ℕ) : ℝ) - 1) * p ^ (m + 2) := by
  induction m with
  | zero => norm_num; nlinarith
  | succ m ih =>
    have hpm : 0 < p ^ (m + 1) := pow_pos hp0 _
    have key : 1 - ((m + 1 + 2 : ℕ) : ℝ) * p ^ (m + 1 + 1) +
        (((m + 1 + 2 : ℕ) : ℝ) - 1) * p ^ (m + 1 + 2) =
        (1 - ((m + 2 : ℕ) : ℝ) * p ^ (m + 1) + (((m + 2 : ℕ) : ℝ) - 1) * p ^ (m + 2)) +
          ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
      push_cast; ring
    rw [key]
    have : 0 < ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
      have : 0 < (1 - p) ^ 2 := by nlinarith
      positivity
    linarith

lemma log_pos' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : 0 < Real.log (1 / p) := by
  apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1

lemma aSeq_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    0 < aSeq p n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold aSeq
  have hl := log_pos' p hp0 hp1
  have := g_pos p hp0 hp1 m
  have e : m + 2 - 1 = m + 1 := by omega
  rw [e]
  positivity

lemma aSeq_mono (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    aSeq p n ≤ aSeq p (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold aSeq
  have hl := log_pos' p hp0 hp1
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 + 1 - 1 = m + 2 := by omega
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ hl.le
  have hpm : 0 < p ^ (m + 1) := pow_pos hp0 _
  have key : 1 - ((m + 2 + 1 : ℕ) : ℝ) * p ^ (m + 2) +
      (((m + 2 + 1 : ℕ) : ℝ) - 1) * p ^ (m + 2 + 1) =
      (1 - ((m + 2 : ℕ) : ℝ) * p ^ (m + 1) + (((m + 2 : ℕ) : ℝ) - 1) * p ^ (m + 2)) +
        ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
    push_cast; ring
  rw [key]
  have : 0 ≤ ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by positivity
  linarith

lemma aSeq_mono' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (i M : ℕ) (hi : 2 ≤ i) (hiM : i ≤ M) :
    aSeq p i ≤ aSeq p M := by
  induction M, hiM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hM ih => exact ih.trans (aSeq_mono p hp0 hp1 M (by omega))

lemma aSeq_one (p : ℝ) : aSeq p 1 = 0 := by simp [aSeq]

lemma lamStar_nonneg (K : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ lamStar K p n := by
  have hb : 0 < bSeq p n := by
    unfold bSeq
    have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
    linarith
  have ha := aSeq_pos p hp0 hp1 n hn
  unfold lamStar
  split_ifs
  · apply mul_nonneg hb.le
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le ha (aSeq_mono p hp0 hp1 n hn)
  · positivity

lemma lamStar_sum_pos (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < ∑ m ∈ Finset.Icc 2 K, lamStar K p m := by
  have hK' : lamStar K p K > 0 := by
    unfold lamStar
    rw [if_neg (lt_irrefl K)]
    have hb : 0 < bSeq p K := by
      unfold bSeq
      have : p ^ K < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
      linarith
    have := aSeq_pos p hp0 hp1 K hK
    positivity
  calc 0 < lamStar K p K := hK'
    _ ≤ _ := Finset.single_le_sum (f := fun m => lamStar K p m)
        (fun m hm => lamStar_nonneg K p hp0 hp1 m (Finset.mem_Icc.1 hm).1)
        (Finset.mem_Icc.2 ⟨hK, le_rfl⟩)

lemma card_prefix (K n : ℕ) (hn : n ≤ K) : (prefixSet K n).card = n := by
  unfold prefixSet
  rw [Fin.card_filter_val_lt]
  omega

/-- `λ^OA_*` as a sum over the prefix sets. -/
lemma lamOA_eq (K : ℕ) (p : ℝ) (S : DS K) :
    lamOA K p S = ∑ n ∈ Finset.Icc 2 K,
      (if S.1 = prefixSet K n then lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m else 0) := by
  classical
  set Λ := ∑ m ∈ Finset.Icc 2 K, lamStar K p m with hΛ
  rw [show lamOA K p S = if (∃ n ∈ Finset.Icc 2 K, S.1 = prefixSet K n) then
    lamStar K p S.1.card / Λ else 0 from rfl]
  by_cases h : ∃ n ∈ Finset.Icc 2 K, S.1 = prefixSet K n
  · rw [if_pos h]
    obtain ⟨n, hn, hSn⟩ := h
    rw [Finset.sum_eq_single n]
    · rw [if_pos hSn, hSn, card_prefix K n (Finset.mem_Icc.1 hn).2]
    · intro b hb hbn
      rw [if_neg]
      intro hSb
      apply hbn
      have := congrArg Finset.card (hSn.symm.trans hSb)
      rwa [card_prefix K n (Finset.mem_Icc.1 hn).2, card_prefix K b (Finset.mem_Icc.1 hb).2,
        eq_comm] at this
    · intro h'; exact absurd hn h'
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg]
    exact fun h' => h ⟨n, hn, h'⟩

lemma sum_lamOA (K : ℕ) (p : ℝ) (G : DS K → ℝ) :
    ∑ S, G S * lamOA K p S = ∑ n ∈ Finset.Icc 2 K, ∑ S : DS K,
      (if S.1 = prefixSet K n then
        G S * (lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) else 0) := by
  simp_rw [lamOA_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun S _ => ?_
  split_ifs <;> simp

lemma inner_eval (K : ℕ) (n : ℕ) (hc : 2 ≤ (prefixSet K n).card) (G : DS K → ℝ) (c : ℝ) :
    ∑ S : DS K, (if S.1 = prefixSet K n then G S * c else 0) = G ⟨prefixSet K n, hc⟩ * c := by
  classical
  have e : ∀ S : DS K, (S.1 = prefixSet K n ↔ S = ⟨prefixSet K n, hc⟩) := by
    intro S; constructor
    · intro h'; exact Subtype.ext h'
    · intro h'; rw [h']
  have : ∀ S : DS K, (if S.1 = prefixSet K n then G S * c else 0) =
      (if S = ⟨prefixSet K n, hc⟩ then G ⟨prefixSet K n, hc⟩ * c else 0) := by
    intro S
    by_cases h : S = ⟨prefixSet K n, hc⟩
    · rw [if_pos ((e S).2 h), if_pos h, h]
    · rw [if_neg (fun h' => h ((e S).1 h')), if_neg h]
  simp_rw [this]
  simp

lemma telescope (K : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (d : ℕ) (hd : d + 2 ≤ K) :
    ∑ n ∈ Finset.Icc (K - d) K, lamStar K p n / bSeq p n = 1 / aSeq p (K - d) := by
  have hb : ∀ n, 1 ≤ n → bSeq p n ≠ 0 := by
    intro n hn
    unfold bSeq
    have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
    linarith
  induction d with
  | zero =>
    simp only [Nat.sub_zero, Finset.Icc_self, Finset.sum_singleton]
    unfold lamStar
    rw [if_neg (lt_irrefl K)]
    field_simp [hb K (by omega)]
  | succ d ih =>
    have hins : Finset.Icc (K - (d + 1)) K = insert (K - (d + 1)) (Finset.Icc (K - d) K) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp; omega), ih (by omega)]
    unfold lamStar
    rw [if_pos (by omega)]
    have e : K - (d + 1) + 1 = K - d := by omega
    rw [e]
    field_simp [hb (K - (d + 1)) (by omega)]
    ring

lemma oa_mem {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : Equiv.Perm (Fin K)) :
    oa p σ ∈ MpRank p σ := by
  classical
  have hrel : ∀ (S : DS K) (X : Fin K), relRank σ S X =
      ((S.1.map σ.toEmbedding).filter (fun y => y ≤ σ X)).card := by
    intro S X
    unfold relRank
    rw [Finset.filter_map, Finset.card_map]
    rfl
  have hr1 : ∀ (S : DS K) (X : Fin K), X ∈ S.1 → 1 ≤ relRank σ S X := by
    intro S X hX
    exact Finset.card_pos.2 ⟨X, Finset.mem_filter.2 ⟨hX, le_rfl⟩⟩
  have hmono : ∀ (S : DS K) (X X' : Fin K), X ∈ S.1 → X' ∈ S.1 → σ X < σ X' →
      relRank σ S X < relRank σ S X' := by
    intro S X X' hX hX' hlt
    unfold relRank
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨X', Finset.mem_filter.2 ⟨hX', le_rfl⟩, ?_⟩
      intro h
      exact absurd (Finset.mem_filter.1 h).2 (not_le.2 hlt)
    · intro k hk
      simp only [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2.trans hlt.le⟩
  have hc : ∀ S : DS K, 0 < (1 - p) / (1 - p ^ S.1.card) := by
    intro S
    have : p ^ S.1.card < 1 := pow_lt_one₀ hp0.le hp1 (by have := S.2; omega)
    apply div_pos <;> linarith
  -- value comparison
  have hval : ∀ (S : DS K) (X X' : Fin K), X ∈ S.1 → X' ∈ S.1 →
      (oa p σ S X' ≤ oa p σ S X ↔ relRank σ S X ≤ relRank σ S X') := by
    intro S X X' hX hX'
    simp only [oa, if_pos hX, if_pos hX']
    rw [mul_le_mul_iff_right₀ (hc S), pow_le_pow_iff_right_of_lt_one₀ hp0 hp1]
    have := hr1 S X hX; have := hr1 S X' hX'
    omega
  refine ⟨⟨?_, ?_, σ, ?_, ?_⟩, ?_⟩
  · intro S X
    refine ⟨fun hX => ?_, fun hX => ?_⟩
    · simp only [oa, if_pos hX]; have := hc S; positivity
    · simp [oa, hX]
  · intro S
    have hn : (S.1.map σ.toEmbedding).card = S.1.card := Finset.card_map _
    calc ∑ X ∈ S.1, oa p σ S X
        = ∑ X ∈ S.1, (1 - p) / (1 - p ^ S.1.card) *
            (fun y => p ^ (((S.1.map σ.toEmbedding).filter (fun z => z ≤ y)).card - 1)) (σ X) := by
          refine Finset.sum_congr rfl fun X hX => ?_
          simp only [oa, if_pos hX, hrel S X]
      _ = (1 - p) / (1 - p ^ S.1.card) * ∑ y ∈ S.1.map σ.toEmbedding,
            p ^ (((S.1.map σ.toEmbedding).filter (fun z => z ≤ y)).card - 1) := by
          rw [Finset.mul_sum, Finset.sum_map]
          rfl
      _ = 1 := by
          rw [sum_rank (fun j => p ^ (j - 1)), hn]
          simp only [Nat.add_sub_cancel]
          rw [geom_sum_eq hp1.ne]
          have h1 : (1 : ℝ) - p ^ S.1.card ≠ 0 := (hc S).ne' |> fun h => by
            intro h0; rw [h0, div_zero] at h; exact h rfl
          have h2 : p - 1 ≠ 0 := by linarith
          have h3 : (1 : ℝ) - p ≠ 0 := by linarith
          field_simp
          ring
  · intro S X X' hX hX' hne
    rw [hval S X X' hX hX']
    constructor
    · intro hle
      rcases lt_or_gt_of_ne (fun h : σ X = σ X' => hne (σ.injective h)) with h | h
      · exact h
      · exact absurd (hmono S X' X hX' hX h) (not_lt.2 hle)
    · intro h; exact (hmono S X X' hX hX' h).le
  · intro S X X' hX hX' hlt
    have := hmono S X X' hX hX' hlt
    have := hr1 S X hX
    simp only [oa, if_pos hX, if_pos hX']
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (hc S).le
    rw [← pow_succ']
    exact pow_le_pow_of_le_one hp0.le hp1.le (by omega)
  · intro S X X' hX hX' hne
    rw [hval S X X' hX hX']
    constructor
    · intro hle
      rcases lt_or_gt_of_ne (fun h : σ X = σ X' => hne (σ.injective h)) with h | h
      · exact h
      · exact absurd (hmono S X' X hX' hX h) (not_lt.2 hle)
    · intro h; exact (hmono S X X' hX hX' h).le

end MTPAux7

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    lamOA K p ∈ simplex K ∧
    ∀ σbar : Equiv.Perm (Fin K), NotTopOne σbar →
      uStar K p ≤ ∑ S, DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p σbar) S * lamOA K p S := by
  classical
  set Λ := ∑ m ∈ Finset.Icc 2 K, lamStar K p m with hΛ
  have hΛpos : 0 < Λ := MTPAux7.lamStar_sum_pos K hK p hp0 hp1
  have hcard : ∀ n ∈ Finset.Icc 2 K, 2 ≤ (prefixSet K n).card := by
    intro n hn
    rw [MTPAux7.card_prefix K n (Finset.mem_Icc.1 hn).2]; exact (Finset.mem_Icc.1 hn).1
  have hnonneg : ∀ S, 0 ≤ lamOA K p S := by
    intro S
    unfold lamOA
    split_ifs
    · exact div_nonneg (MTPAux7.lamStar_nonneg K p hp0 hp1 _ S.2) hΛpos.le
    · exact le_rfl
  refine ⟨⟨hnonneg, ?_⟩, ?_⟩
  · have := MTPAux7.sum_lamOA K p (fun _ => 1)
    simp only [one_mul] at this
    rw [this]
    rw [Finset.sum_congr rfl (fun n hn => by
      have := MTPAux7.inner_eval K n (hcard n hn) (fun _ => 1) (lamStar K p n / Λ)
      simp only [one_mul] at this
      exact this)]
    rw [← Finset.sum_div, div_self hΛpos.ne']
  · intro σbar hσ
    set k := σbar.symm ⟨0, by omega⟩ with hk
    have hσk : (σbar k).val = 0 := by simp [hk]
    have hk1 : 1 ≤ k.val := by
      have := hσ k hσk; omega
    -- the value at `σ̂_k`
    have hval : ∑ S, DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat k)) S * lamOA K p S =
        uStar K p := by
      rw [MTPAux7.sum_lamOA]
      simp_rw [← hΛ]
      set M := k.val + 1 with hM
      have hterm : ∀ n ∈ Finset.Icc 2 K,
          (∑ S : DS K, if S.1 = prefixSet K n then
            DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat k)) S * (lamStar K p n / Λ)
            else 0) =
          if M ≤ n then aSeq p M / Λ * (lamStar K p n / bSeq p n) else 0 := by
        intro n hn
        rw [MTPAux7.inner_eval K n (hcard n hn)
          (fun S => DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat k)) S)
          (lamStar K p n / Λ)]
        rw [lemma_6 K hK p hp0 hp1 k hk1]
        have hnK := (Finset.mem_Icc.1 hn).2
        by_cases hkn : M ≤ n
        · have hmem : k ∈ prefixSet K n := by simp [prefixSet]; omega
          rw [if_pos hmem, if_pos hkn]
          have hrr : relRank (1 : Equiv.Perm (Fin K)) ⟨prefixSet K n, hcard n hn⟩ k = M := by
            unfold relRank
            have : (prefixSet K n).filter (fun x => (1 : Equiv.Perm (Fin K)) x ≤
                (1 : Equiv.Perm (Fin K)) k) = Finset.univ.filter (fun x : Fin K => x.val < M) := by
              ext x
              simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and,
                Equiv.Perm.one_apply, Fin.le_def]
              omega
            simp only at this ⊢
            rw [this, Fin.card_filter_val_lt]
            omega
          rw [hrr]
          rw [show ((⟨prefixSet K n, hcard n hn⟩ : DS K).1.card) = n from
            MTPAux7.card_prefix K n hnK]
          ring
        · have hmem : k ∉ prefixSet K n := by simp [prefixSet]; omega
          rw [if_neg hmem, if_neg hkn, zero_mul]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
      have hfilt : (Finset.Icc 2 K).filter (fun n => M ≤ n) = Finset.Icc (K - (K - M)) K := by
        ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      have hMK : M ≤ K := by have := k.2; omega
      rw [hfilt, ← Finset.mul_sum, MTPAux7.telescope K p hp0 hp1 (K - M) (by omega)]
      have e : K - (K - M) = M := by omega
      rw [e]
      have ha := MTPAux7.aSeq_pos p hp0 hp1 M (by omega)
      unfold uStar
      rw [← hΛ]
      field_simp
    rw [← hval]
    obtain ⟨fh, hfh, hdom⟩ := lemma_4 K hK p hp0 hp1 k (oa p 1) (MTPAux7.oa_mem p hp0 hp1 1)
      σbar hσk (oa p σbar) (MTPAux7.oa_mem p hp0 hp1 σbar)
    have hd := hdom (lamOA K p) ⟨hnonneg, by
      have := MTPAux7.sum_lamOA K p (fun _ => 1)
      simp only [one_mul] at this
      rw [this]
      rw [Finset.sum_congr rfl (fun n hn => by
        have := MTPAux7.inner_eval K n (hcard n hn) (fun _ => 1) (lamStar K p n / Λ)
        simp only [one_mul] at this
        exact this)]
      rw [← Finset.sum_div, div_self hΛpos.ne']⟩
    unfold Dlam at hd
    calc ∑ S, DS_ (oa p 1) (oa p (sigmaHat k)) S * lamOA K p S
        ≤ ∑ S, DS_ (oa p 1) fh S * lamOA K p S := by
          apply Finset.sum_le_sum
          intro S _
          apply mul_le_mul_of_nonneg_right _ (hnonneg S)
          exact (lemma_5 K hK p hp0 hp1 k hk1 S).2.2 _ (MTPAux7.oa_mem p hp0 hp1 1) fh hfh
      _ = ∑ S, lamOA K p S * DS_ (oa p 1) fh S := by simp_rw [mul_comm]
      _ ≤ ∑ S, lamOA K p S * DS_ (oa p 1) (oa p σbar) S := hd
      _ = _ := by simp_rw [mul_comm]
