-- Prove2me | solution 1 for RobustPrefLearn.MTP.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:18:09.919736+00:00
-- url     : https://prove2.me/submissions/8a037841-6c16-49b9-8493-9302caf84284

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA
import Theorems.Thm_RobustPrefLearn_MTP_lemma_6

open scoped ENNReal

namespace MTPAux8
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

lemma muSeq_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (j : ℕ) (hj : 2 ≤ j) : 0 < muSeq p j := by
  unfold muSeq bSeq
  have ha := aSeq_pos p hp0 hp1 j hj
  split_ifs with h
  · subst h
    have : p ^ 2 < 1 := pow_lt_one₀ hp0.le hp1 (by norm_num)
    apply div_pos _ ha; linarith
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    apply div_pos _ ha
    have : p ^ (k + 1) < p ^ k := pow_lt_pow_right_of_lt_one₀ hp0 hp1 (by omega)
    linarith

lemma sum_shift (h : ℕ → ℝ) (K : ℕ) :
    ∑ i ∈ Finset.range K, (if 1 ≤ i then h (i + 1) else 0) = ∑ j ∈ Finset.Icc 2 K, h j := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    · rw [if_pos (show 1 ≤ K by omega), Finset.sum_Icc_succ_top (by omega)]

lemma sum_fin_shift {K : ℕ} (h : ℕ → ℝ) :
    ∑ m : Fin K, (if 1 ≤ m.val then h (m.val + 1) else 0) = ∑ j ∈ Finset.Icc 2 K, h j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if 1 ≤ i then h (i + 1) else 0) K]
  exact sum_shift h K

lemma hv {K : ℕ} (m k : Fin K) : ((sigmaHat m) k).val =
    if k.val < m.val then k.val + 1 else if k.val = m.val then 0 else k.val := by
  unfold sigmaHat
  by_cases h : k ≤ m
  · rw [Fin.coe_cycleRange_of_le h]
    by_cases h' : k = m
    · subst h'; simp
    · have : k.val < m.val := lt_of_le_of_ne h (fun e => h' (Fin.ext e))
      rw [if_neg h', if_pos this]
  · rw [Fin.cycleRange_of_gt (not_le.1 h)]
    have : ¬ k.val < m.val := fun e => h (le_of_lt e)
    have : ¬ k.val = m.val := fun e => h (le_of_eq (Fin.ext e))
    simp_all

lemma notTop_hat {K : ℕ} (m : Fin K) (hm : 1 ≤ m.val) : NotTopOne (sigmaHat m) := by
  intro k hk
  rw [hv] at hk
  split_ifs at hk with h1 h2 <;> omega

/-- Generic sum rewriting `∑_{σ ∈ Σ̄} F σ µ*(σ)`. -/
lemma sum_muStar {K : ℕ} (p : ℝ) (F : Equiv.Perm (Fin K) → ℝ) :
    ∑ σbar ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin K) => NotTopOne σ),
        F σbar * muStar K p σbar =
      ∑ m : Fin K, (if 1 ≤ m.val then
        F (sigmaHat m) * (muSeq p (m.val + 1) / ∑ j ∈ Finset.Icc 2 K, muSeq p j) else 0) := by
  classical
  unfold muStar
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : 1 ≤ m.val
  · rw [if_pos hm]
    have : ∀ σ : Equiv.Perm (Fin K), (F σ * if 1 ≤ m.val ∧ σ = sigmaHat m then
        muSeq p (m.val + 1) / ∑ j ∈ Finset.Icc 2 K, muSeq p j else 0) =
        if σ = sigmaHat m then
          F (sigmaHat m) * (muSeq p (m.val + 1) / ∑ j ∈ Finset.Icc 2 K, muSeq p j) else 0 := by
      intro σ
      by_cases hσ : σ = sigmaHat m
      · subst hσ; simp [hm]
      · simp [hσ]
    simp_rw [this]
    rw [Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_filter.2 ⟨Finset.mem_univ _, notTop_hat m hm⟩)]
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro σ _
    simp [hm]

end MTPAux8

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ σbar : Equiv.Perm (Fin K), 0 ≤ muStar K p σbar) ∧
    ∑ σbar ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin K) => NotTopOne σ), muStar K p σbar = 1 ∧
    ∀ S : DS K,
      ∑ σbar ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin K) => NotTopOne σ),
        DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p σbar) S * muStar K p σbar ≤ lStar K p := by
  classical
  set Z := ∑ j ∈ Finset.Icc 2 K, muSeq p j with hZ
  have hZpos : 0 < Z := by
    calc 0 < muSeq p K := MTPAux8.muSeq_pos p hp0 hp1 K hK
      _ ≤ Z := Finset.single_le_sum (f := fun j => muSeq p j)
          (fun j hj => (MTPAux8.muSeq_pos p hp0 hp1 j (Finset.mem_Icc.1 hj).1).le)
          (Finset.mem_Icc.2 ⟨hK, le_rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro σ
    unfold muStar
    apply Finset.sum_nonneg
    intro m _
    split_ifs with h
    · exact div_nonneg (MTPAux8.muSeq_pos p hp0 hp1 _ (by omega)).le hZpos.le
    · exact le_rfl
  · have := MTPAux8.sum_muStar (K := K) p (fun _ => 1)
    simp only [one_mul] at this
    rw [this]
    have e : ∀ m : Fin K, (if 1 ≤ m.val then muSeq p (m.val + 1) / Z else 0) =
        (if 1 ≤ m.val then (fun j => muSeq p j / Z) (m.val + 1) else 0) := fun _ => rfl
    rw [Finset.sum_congr rfl (fun m _ => e m), MTPAux8.sum_fin_shift (K := K) (fun j => muSeq p j / Z), ← Finset.sum_div,
      div_self hZpos.ne']
  · intro S
    rw [MTPAux8.sum_muStar]
    set n := S.1.card with hn
    have hn2 : 2 ≤ n := S.2
    have hbn : 0 < bSeq p n := by
      unfold bSeq; have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega); linarith
    set r : Fin K → ℕ := fun X => (S.1.filter (fun k => k ≤ X)).card with hr
    -- the bound `B`
    set B : ℕ → ℝ := fun i => if i = 1 then 0 else if i = 2 then bSeq p 2
      else bSeq p i - bSeq p (i - 1) with hB
    have hBsum : ∀ N, 2 ≤ N → ∑ j ∈ Finset.range N, B (j + 1) = bSeq p N := by
      intro N hN
      induction N, hN using Nat.le_induction with
      | base => simp [hB, Finset.sum_range_succ]
      | succ N hN ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [hB]
        rw [if_neg (by omega), if_neg (by omega)]
        simp
    -- rewrite each term with Lemma 6
    have hterm : ∀ m : Fin K, (if 1 ≤ m.val then
        DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat m)) S * (muSeq p (m.val + 1) / Z)
        else 0) ≤ (if m ∈ S.1 then B (r m) else 0) / bSeq p n / Z := by
      intro m
      by_cases hm : 1 ≤ m.val
      · rw [if_pos hm, lemma_6 K hK p hp0 hp1 m hm S]
        by_cases hmS : m ∈ S.1
        · rw [if_pos hmS, if_pos hmS]
          have hrr : relRank (1 : Equiv.Perm (Fin K)) S m = r m := by
            unfold relRank; rfl
          rw [hrr, ← hn]
          rw [show aSeq p (r m) / bSeq p n * (muSeq p (m.val + 1) / Z) =
            aSeq p (r m) * muSeq p (m.val + 1) / bSeq p n / Z by ring]
          gcongr
          -- the key estimate `𝔞_i µ_M ≤ B i`
          have hi1 : 1 ≤ r m := Finset.card_pos.2 ⟨m, Finset.mem_filter.2 ⟨hmS, le_rfl⟩⟩
          have hiM : r m ≤ m.val + 1 := by
            calc r m ≤ (Finset.univ.filter (fun k : Fin K => k ≤ m)).card := by
                  apply Finset.card_le_card
                  intro k hk
                  simp only [Finset.mem_filter] at hk ⊢
                  exact ⟨Finset.mem_univ _, hk.2⟩
              _ = (Finset.univ.filter (fun k : Fin K => k.val < m.val + 1)).card := by
                  congr 1; ext k
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
                  omega
              _ = min K (m.val + 1) := Fin.card_filter_val_lt
              _ ≤ m.val + 1 := min_le_right _ _
          set i := r m with hi
          set M := m.val + 1 with hM
          have hM2 : 2 ≤ M := by omega
          have haM := MTPAux8.aSeq_pos p hp0 hp1 M hM2
          rcases Nat.lt_or_ge i 2 with h1 | h2
          · have : i = 1 := by omega
            rw [this, MTPAux8.aSeq_one]
            simp [hB]
          · have hai := MTPAux8.aSeq_pos p hp0 hp1 i h2
            have hmono := MTPAux8.aSeq_mono' p hp0 hp1 i M h2 hiM
            by_cases hM2' : M = 2
            · have : i = 2 := by omega
              rw [this, hM2']
              simp only [hB, muSeq, if_true]
              rw [if_neg (by norm_num)]
              rw [mul_div_cancel₀ _ (MTPAux8.aSeq_pos p hp0 hp1 2 le_rfl).ne']
            · have hmu : muSeq p M = p ^ (M - 1) * (1 - p) / aSeq p M := by
                unfold muSeq bSeq
                rw [if_neg hM2']
                congr 1
                obtain ⟨k, hk⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
                rw [hk]; simp [pow_succ]; ring
              rw [hmu]
              have hp1' : 0 < 1 - p := by linarith
              by_cases hi2 : i = 2
              · simp only [hB]
                rw [if_neg (by omega), if_pos hi2]
                rw [hi2] at hmono
                unfold bSeq
                have hpM : p ^ (M - 1) ≤ 1 := pow_le_one₀ hp0.le hp1.le
                rw [hi2, mul_div_assoc']
                rw [div_le_iff₀ haM]
                have : aSeq p 2 * (p ^ (M - 1) * (1 - p)) ≤ aSeq p M * (1 - p) := by
                  have := MTPAux8.aSeq_pos p hp0 hp1 2 le_rfl
                  calc aSeq p 2 * (p ^ (M - 1) * (1 - p)) ≤ aSeq p M * (1 * (1 - p)) := by
                        gcongr
                    _ = _ := by ring
                have h3 : (1 - p ^ 2) * aSeq p M = aSeq p M * (1 - p) + p * (1 - p) * aSeq p M := by
                  ring
                have h4 : 0 ≤ p * (1 - p) * aSeq p M := by positivity
                linarith
              · simp only [hB]
                rw [if_neg (by omega), if_neg hi2]
                have hbi : bSeq p i - bSeq p (i - 1) = p ^ (i - 1) * (1 - p) := by
                  unfold bSeq
                  obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
                  rw [hk]; simp [pow_succ]; ring
                rw [hbi, mul_div_assoc', div_le_iff₀ haM]
                have hpp : p ^ (M - 1) ≤ p ^ (i - 1) :=
                  pow_le_pow_of_le_one hp0.le hp1.le (by omega)
                calc aSeq p i * (p ^ (M - 1) * (1 - p)) ≤ aSeq p M * (p ^ (i - 1) * (1 - p)) := by
                      gcongr
                  _ = _ := by ring
        · rw [if_neg hmS, if_neg hmS]; simp
      · rw [if_neg hm]
        by_cases hmS : m ∈ S.1
        · rw [if_pos hmS]
          -- `m` is version 1, hence first in `S`, rank 1
          have : r m = 1 := by
            have hm0 : m.val = 0 := by omega
            simp only [hr]
            rw [Finset.card_eq_one]
            refine ⟨m, ?_⟩
            ext k
            simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨_, hk⟩; exact Fin.ext (by rw [Fin.le_def] at hk; omega)
            · rintro rfl; exact ⟨hmS, le_rfl⟩
          rw [this]; simp [hB]
        · rw [if_neg hmS]; simp
    calc _ ≤ ∑ m : Fin K, (if m ∈ S.1 then B (r m) else 0) / bSeq p n / Z :=
          Finset.sum_le_sum fun m _ => hterm m
      _ = (∑ m ∈ S.1, B (r m)) / bSeq p n / Z := by
          rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_ite_mem, Finset.univ_inter]
      _ = 1 / Z := by
          rw [show (∑ m ∈ S.1, B (r m)) = ∑ j ∈ Finset.range n, B (j + 1) from
            MTPAux8.sum_rank B S.1, hBsum n hn2, div_self hbn.ne']
      _ = lStar K p := rfl
