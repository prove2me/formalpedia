-- Prove2me | solution 1 for RobustPrefLearn.MTP.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T15:41:07.777194+00:00
-- url     : https://prove2.me/submissions/a9f2c83e-843d-444c-8f41-b4b2a8fd24ab

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp
import Theorems.Thm_RobustPrefLearn_MTP_lemma_8
import Theorems.Thm_RobustPrefLearn_MTP_lemma_9
import Theorems.Thm_RobustPrefLearn_MTP_lemma_6

open scoped ENNReal Topology

namespace MTPAux
open RobustPrefLearn.MTP

lemma toHist_snoc {K t : ℕ} (w : Fin t → Step K) (x : Step K) :
    toHist (Fin.snoc w x : Fin (t + 1) → Step K) = x :: toHist w := by
  unfold toHist
  rw [List.ofFn_succ']
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma toHist_zero {K : ℕ} (v : Fin 0 → Step K) : toHist v = [] := by
  simp [toHist]

lemma survives_cons {K : ℕ} (π : Policy K) (x : Step K) (h : List (Step K)) :
    survives π (x :: h) ↔ ¬ π.stop (x :: h) ∧ survives π h := by
  unfold survives
  constructor
  · intro H
    refine ⟨by simpa using H 0 (by simp), fun j hj => ?_⟩
    simpa using H (j + 1) (by simp; omega)
  · rintro ⟨H0, H⟩ j hj
    cases j with
    | zero => simpa using H0
    | succ j => simpa using H j (by simp at hj; omega)

lemma stopsAt_cons {K : ℕ} (π : Policy K) (x : Step K) (h : List (Step K)) :
    stopsAt π (x :: h) ↔ π.stop (x :: h) ∧ survives π h := by
  unfold stopsAt survives
  constructor
  · rintro ⟨H0, H⟩
    refine ⟨H0, fun j hj => ?_⟩
    simpa using H (j + 1) (by omega) (by simp; omega)
  · rintro ⟨H0, H⟩
    refine ⟨H0, fun j hj1 hj2 => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simpa using H j (by simp at hj2; omega)

lemma step_sum {K : ℕ} (p : ℝ) (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (h : List (Step K)) :
    ∑ x : Step K, π.disp h x.1 * ENNReal.ofReal (f x.1 x.2) = 1 := by
  rw [Fintype.sum_prod_type]
  have hS : ∀ S : DS K, ∑ X : Fin K, ENNReal.ofReal (f S X) = 1 := by
    intro S
    have hnn : ∀ X, 0 ≤ f S X := by
      intro X
      by_cases hX : X ∈ S.1
      · exact ((hf.1 S X).1 hX).le
      · exact ((hf.1 S X).2 hX).ge
    rw [← ENNReal.ofReal_sum_of_nonneg (fun X _ => hnn X)]
    have : ∑ X : Fin K, f S X = ∑ X ∈ S.1, f S X := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro X _ hX
      exact (hf.1 S X).2 hX
    rw [this, hf.2.1 S, ENNReal.ofReal_one]
  simp_rw [← Finset.mul_sum, hS, mul_one]
  exact hπ h

open Classical in
lemma key_step {K : ℕ} (p : ℝ) (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (t : ℕ) :
    (∑ v : Fin (t + 1) → Step K,
        if stopsAt π (toHist v) then pathProb π f (toHist v) else 0) +
      probGT π f (t + 1) = probGT π f t := by
  unfold probGT
  rw [← Finset.sum_add_distrib]
  rw [← (Fin.snocEquiv (fun _ => Step K)).sum_comp]
  have hsn : ∀ i : Step K × (Fin t → Step K),
      (Fin.snocEquiv (fun _ => Step K)) i = (Fin.snoc i.2 i.1 : Fin (t + 1) → Step K) :=
    fun i => rfl
  simp only [hsn, toHist_snoc, stopsAt_cons, survives_cons]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : ∀ x : Step K,
      ((if π.stop (x :: toHist w) ∧ survives π (toHist w) then
          pathProb π f (x :: toHist w) else 0) +
        (if ¬ π.stop (x :: toHist w) ∧ survives π (toHist w) then
          pathProb π f (x :: toHist w) else 0)) =
      (if survives π (toHist w) then pathProb π f (toHist w) else 0) *
        (π.disp (toHist w) x.1 * ENNReal.ofReal (f x.1 x.2)) := by
    intro x
    obtain ⟨S, X⟩ := x
    simp only [pathProb]
    by_cases hs : survives π (toHist w) <;> by_cases hst : π.stop ((S, X) :: toHist w) <;>
      simp [hs, hst, mul_assoc]
  simp_rw [this, ← Finset.mul_sum]
  rw [step_sum p π hπ f hf, mul_one]

open Classical in
lemma partial_eq {K : ℕ} (p : ℝ) (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (t : ℕ) :
    probGT π f t + ∑ s ∈ Finset.range (t + 1), ∑ v : Fin s → Step K,
        (if stopsAt π (toHist v) then pathProb π f (toHist v) else 0) = 1 := by
  induction t with
  | zero =>
    unfold probGT
    rw [Finset.sum_range_one]
    rw [← Finset.sum_add_distrib]
    rw [Fintype.sum_unique]
    simp only [toHist_zero, pathProb]
    unfold survives stopsAt
    by_cases h0 : π.stop [] <;> simp [h0]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih, ← key_step p π hπ f hf t]
    ring

theorem probStop_eq_one {K : ℕ} (p : ℝ) (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (hE : expTau π f < ⊤) : probStop π f = 1 := by
  classical
  set B : ℕ → ℝ≥0∞ := fun s => ∑ v : Fin s → Step K,
    (if stopsAt π (toHist v) then pathProb π f (toHist v) else 0) with hB
  have hP : probStop π f = ∑' s, B s := by
    unfold probStop; rfl
  rw [hP]
  apply le_antisymm
  · refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    cases n with
    | zero => simp
    | succ n =>
      rw [← partial_eq p π hπ f hf n]
      exact le_add_self
  · have hA : Filter.Tendsto (fun t => probGT π f t) Filter.atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hE.ne
    have h1 : ∀ t, 1 ≤ probGT π f t + ∑' s, B s := by
      intro t
      rw [← partial_eq p π hπ f hf t]
      gcongr
      exact ENNReal.sum_le_tsum _
    have := Filter.Tendsto.add_const (∑' s, B s) hA
    rw [zero_add] at this
    exact ge_of_tendsto' this h1

end MTPAux

namespace MTPAux
open RobustPrefLearn.MTP

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

lemma aSeq_pos (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    0 < aSeq p n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold aSeq
  have hl : 0 < Real.log (1 / p) := by
    apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1
  have := g_pos p hp0 hp1 m
  have e : m + 2 - 1 = m + 1 := by omega
  rw [e]
  positivity

lemma aSeq_mono (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    aSeq p n ≤ aSeq p (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold aSeq
  have hl : 0 < Real.log (1 / p) := by
    apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1
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

lemma card_topSet {K : ℕ} (σ : Equiv.Perm (Fin K)) (n : ℕ) (hn : n ≤ K) :
    (topSet σ n).card = n := by
  have : topSet σ n = (Finset.univ.filter (fun i : Fin K => i.val < n)).map σ.symm.toEmbedding := by
    ext X
    simp [topSet]
  rw [this, Finset.card_map, Fin.card_filter_val_lt]
  omega

lemma mle_nonempty {K : ℕ} [NeZero K] (p : ℝ) (h : List (Step K)) : (mle p h).Nonempty := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_max_image Finset.univ (fun σ => loglikOA p σ h)
    Finset.univ_nonempty
  exact ⟨σ, by simp [mle]; exact fun σ' => hσ σ' (Finset.mem_univ _)⟩

theorem mtp_admissible {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (S1 : DS K) (β : ℝ) : Admissible (mtp p S1 β) := by
  classical
  intro h
  simp only [mtp]
  by_cases hh : h = []
  · simp [hh]
  · simp only [hh, if_false]
    rw [← Finset.mul_sum]
    have hinner : ∀ σ ∈ mle p h, ∑ S : DS K, ∑ n ∈ Finset.Icc 2 K,
        (if S.1 = topSet σ n then
          ENNReal.ofReal (lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) else 0) = 1 := by
      intro σ _
      rw [Finset.sum_comm]
      have : ∀ n ∈ Finset.Icc 2 K, ∑ S : DS K,
          (if S.1 = topSet σ n then
            ENNReal.ofReal (lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) else 0) =
          ENNReal.ofReal (lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) := by
        intro n hn
        obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
        have hc : 2 ≤ (topSet σ n).card := by rw [card_topSet σ n hn2]; exact hn1
        have e : ∀ S : DS K, (S.1 = topSet σ n ↔ S = ⟨topSet σ n, hc⟩) := by
          intro S; constructor
          · intro h'; exact Subtype.ext h'
          · intro h'; rw [h']
        simp_rw [e]
        simp
      rw [Finset.sum_congr rfl this]
      have hpos := lamStar_sum_pos K hK p hp0 hp1
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n hn =>
        div_nonneg (lamStar_nonneg K p hp0 hp1 n (Finset.mem_Icc.1 hn).1) hpos.le)]
      rw [← Finset.sum_div, div_self hpos.ne', ENNReal.ofReal_one]
    rw [Finset.sum_comm, Finset.sum_congr rfl hinner]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    apply ENNReal.inv_mul_cancel
    · simpa using (mle_nonempty p h).ne_empty
    · simp

end MTPAux

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

namespace MTPAux1i
open RobustPrefLearn.MTP

/-- `a log c + a - c b ≤ a log (a/b)` (from `log x ≤ x - 1`), with the convention that the
right-hand side is `a L` where `L = log(a/b)` whenever `a > 0`. -/
lemma plog (a b c L : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c)
    (hpos : 0 < a → 0 < b ∧ L = Real.log (a / b)) :
    a * Real.log c + a - c * b ≤ a * L := by
  rcases ha.lt_or_eq with ha | ha
  · obtain ⟨hb, rfl⟩ := hpos ha
    have h1 : Real.log (b * c / a) ≤ b * c / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (b * c / a) = Real.log b + Real.log c - Real.log a := by
      rw [Real.log_div (by positivity) ha.ne', Real.log_mul hb.ne' hc.ne']
    rw [h2] at h1
    rw [Real.log_div ha.ne' hb.ne']
    have h3 : a * (b * c / a - 1) = b * c - a := by field_simp
    nlinarith
  · subst ha; simp; positivity

lemma f_nonneg {K : ℕ} {p : ℝ} {f : Pref K} (hf : f ∈ (Mp p : Set (Pref K))) (S : DS K)
    (X : Fin K) : 0 ≤ f S X := by
  by_cases hX : X ∈ S.1
  · exact ((hf.1 S X).1 hX).le
  · exact ((hf.1 S X).2 hX).ge

lemma f_sum_univ {K : ℕ} {p : ℝ} {f : Pref K} (hf : f ∈ (Mp p : Set (Pref K))) (S : DS K) :
    ∑ X : Fin K, f S X = 1 := by
  rw [← hf.2.1 S]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro X _ hX
  exact (hf.1 S X).2 hX

lemma DS_eq_univ {K : ℕ} {p : ℝ} {f : Pref K} (hf : f ∈ (Mp p : Set (Pref K))) (g : Pref K)
    (S : DS K) : DS_ f g S = ∑ X : Fin K, f S X * Real.log (f S X / g S X) := by
  unfold DS_
  apply Finset.sum_subset (Finset.subset_univ _)
  intro X _ hX
  simp [(hf.1 S X).2 hX]

/-- Gibbs' inequality. -/
lemma DS_nonneg {K : ℕ} {p : ℝ} {f g : Pref K} (hf : f ∈ (Mp p : Set (Pref K)))
    (hg : g ∈ (Mp p : Set (Pref K))) (S : DS K) : 0 ≤ DS_ f g S := by
  unfold DS_
  have : ∑ X ∈ S.1, (f S X * Real.log 1 + f S X - 1 * g S X) ≤
      ∑ X ∈ S.1, f S X * Real.log (f S X / g S X) := by
    apply Finset.sum_le_sum
    intro X hX
    exact plog _ _ _ _ (f_nonneg hf S X) (f_nonneg hg S X) one_pos
      (fun _ => ⟨(hg.1 S X).1 hX, rfl⟩)
  have h2 : ∑ X ∈ S.1, (f S X * Real.log 1 + f S X - 1 * g S X) = 0 := by
    simp only [Real.log_one, mul_zero, zero_add, one_mul]
    rw [Finset.sum_sub_distrib, hf.2.1 S, hg.2.1 S, sub_self]
  linarith

/-- The top-ranked version does not depend on the choice of ranking. -/
lemma top_unique {K : ℕ} (f : Pref K) (σ1 σ2 : Equiv.Perm (Fin K)) (h1 : Ranks f σ1)
    (h2 : Ranks f σ2) (k : Fin K) (hk : (σ1 k).val = 0) : (σ2 k).val = 0 := by
  by_contra hne
  set j := σ2.symm ⟨0, by have := (σ1 k).2; omega⟩ with hj
  have hj0 : σ2 j = ⟨0, by have := (σ1 k).2; omega⟩ := by simp [hj]
  have hjk : j ≠ k := by
    intro e; apply hne; rw [← e, hj0]
  have hcard : 2 ≤ ({k, j} : Finset (Fin K)).card := by
    rw [Finset.card_pair hjk.symm]
  set S : DS K := ⟨{k, j}, hcard⟩
  have hkS : k ∈ S.1 := by simp [S]
  have hjS : j ∈ S.1 := by simp [S]
  have a1 : f S k ≤ f S j := (h2 S j k hjS hkS hjk).2 (by
    rw [Fin.lt_def, hj0]; simp only; omega)
  have hσ1j : (σ1 j).val ≠ 0 := by
    intro e; apply hjk; exact σ1.injective (Fin.ext (by rw [e, hk]))
  have a2 : f S j ≤ f S k := (h1 S k j hkS hjS hjk.symm).2 (by
    rw [Fin.lt_def]; omega)
  have a3 := (h1 S j k hjS hkS hjk).1 a1
  rw [Fin.lt_def] at a3
  omega

lemma isTop_of_rank {K : ℕ} (f : Pref K) (σ : Equiv.Perm (Fin K)) (hR : Ranks f σ) (k : Fin K)
    (hk : IsTop f k) : (σ k).val = 0 := by
  obtain ⟨σ1, h1, hk1⟩ := hk
  exact top_unique f σ1 σ h1 hR k hk1

/-- `M̄_p(f)` is nonempty. -/
lemma alt_nonempty {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) : ∃ g, g ∈ alt p f := by
  obtain ⟨σf, hR, _⟩ := hf.2.2
  let i0 : Fin K := ⟨0, by omega⟩
  let i1 : Fin K := ⟨1, by omega⟩
  let σ' : Equiv.Perm (Fin K) := σf.trans (Equiv.swap i0 i1)
  have hmem := MTPAux7.oa_mem p hp0 hp1 σ'
  refine ⟨oa p σ', hmem.1, fun k k' hk hk' e => ?_⟩
  subst e
  have a1 := isTop_of_rank f σf hR k hk
  have a2 := isTop_of_rank (oa p σ') σ' hmem.2 k hk'
  have : σf k = i0 := Fin.ext a1
  simp only [σ', Equiv.trans_apply, this, Equiv.swap_apply_left] at a2
  simp [i1] at a2

lemma card_DS_pos {K : ℕ} (hK : 2 ≤ K) : 0 < Fintype.card (DS K) := by
  apply Fintype.card_pos_iff.2
  exact ⟨⟨Finset.univ, by simp; omega⟩⟩

/-- Chernoff's information is positive. -/
lemma Istar_pos {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) : Istar p f ≠ 0 := by
  classical
  set N := Fintype.card (DS K)
  have hN : (0 : ℝ) < N := by exact_mod_cast card_DS_pos hK
  set L := Real.log (1 / p) with hL
  have hLpos : 0 < L := by
    apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1
  set η := (1 - p) / (1 + p) * L with hη
  have hηpos : 0 < η := by
    have : 0 < 1 - p := by linarith
    positivity
  let lu : DS K → ℝ := fun _ => 1 / N
  have hlu : lu ∈ simplex K := by
    refine ⟨fun _ => by positivity, ?_⟩
    simp only [lu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hN.ne'
  have key : ∀ g ∈ alt p f, η / N ≤ Dlam lu f g := by
    intro g hg
    obtain ⟨σf, hRf, hPf⟩ := hf.2.2
    obtain ⟨σg, hRg, hPg⟩ := hg.1.2.2
    set X1 := σf.symm ⟨0, by omega⟩ with hX1
    set k' := σg.symm ⟨0, by omega⟩ with hk'
    have hσfX1 : σf X1 = ⟨0, by omega⟩ := by simp [hX1]
    have hσgk : σg k' = ⟨0, by omega⟩ := by simp [hk']
    have htf : IsTop f X1 := ⟨σf, hRf, by rw [hσfX1]⟩
    have htg : IsTop g k' := ⟨σg, hRg, by rw [hσgk]⟩
    have hne : X1 ≠ k' := hg.2 X1 k' htf htg
    have hcard : 2 ≤ ({X1, k'} : Finset (Fin K)).card := by rw [Finset.card_pair hne]
    set S0 : DS K := ⟨{X1, k'}, hcard⟩
    have h1S : X1 ∈ S0.1 := by simp [S0]
    have h2S : k' ∈ S0.1 := by simp [S0]
    -- the four probabilities
    set f1 := f S0 X1; set f2 := f S0 k'; set g1 := g S0 X1; set g2 := g S0 k'
    have hf1 : 0 < f1 := (hf.1 S0 X1).1 h1S
    have hf2 : 0 < f2 := (hf.1 S0 k').1 h2S
    have hg1 : 0 < g1 := (hg.1.1 S0 X1).1 h1S
    have hg2 : 0 < g2 := (hg.1.1 S0 k').1 h2S
    have hfs : f1 + f2 = 1 := by
      have := hf.2.1 S0; simp only [S0] at this; rwa [Finset.sum_pair hne] at this
    have hgs : g1 + g2 = 1 := by
      have := hg.1.2.1 S0; simp only [S0] at this; rwa [Finset.sum_pair hne] at this
    have hfp : f2 ≤ p * f1 := hPf S0 X1 k' h1S h2S (by
      rw [hσfX1, Fin.lt_def]; simp only
      have : σf k' ≠ ⟨0, by omega⟩ := by
        intro e; apply hne; rw [hX1, ← e]; simp
      have : (σf k').val ≠ 0 := fun e => this (Fin.ext e)
      omega)
    have hgp : g1 ≤ p * g2 := hPg S0 k' X1 h2S h1S (by
      rw [hσgk, Fin.lt_def]; simp only
      have : σg X1 ≠ ⟨0, by omega⟩ := by
        intro e; apply hne; rw [hk', ← e]; simp
      have : (σg X1).val ≠ 0 := fun e => this (Fin.ext e)
      omega)
    -- lower bound on `D_{S0}`
    have hD : η ≤ DS_ f g S0 := by
      unfold DS_
      simp only [S0]
      rw [Finset.sum_pair hne]
      have e1 := plog f1 g1 (1 / p) (Real.log (f1 / g1)) hf1.le hg1.le (by positivity)
        (fun _ => ⟨hg1, rfl⟩)
      have e2 := plog f2 g2 p (Real.log (f2 / g2)) hf2.le hg2.le hp0
        (fun _ => ⟨hg2, rfl⟩)
      have hlogp : Real.log p = -L := by
        rw [hL, one_div, Real.log_inv, neg_neg]
      rw [hlogp] at e2
      rw [← hL] at e1
      -- algebra
      have hg2e : g2 = 1 - g1 := by linarith
      have hX : 0 ≤ 1 - 1 / p * g1 - p * g2 := by
        have e : 1 - 1 / p * g1 - p * g2 = (1 - p) * (p - g1 * (1 + p)) / p := by
          rw [hg2e]; field_simp; ring
        rw [e]
        apply div_nonneg _ hp0.le
        apply mul_nonneg (by linarith)
        nlinarith
      have hB : (1 - p) / (1 + p) ≤ f1 - f2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have hfg : (1 - p) / (1 + p) * L ≤ (f1 - f2) * L := by gcongr
      rw [hη]
      nlinarith [e1, e2]
    -- `D_λ ≥ D_{S0}/N`
    unfold Dlam
    calc η / N ≤ lu S0 * DS_ f g S0 := by
          simp only [lu]; rw [div_mul_eq_mul_div, one_mul]; gcongr
      _ ≤ ∑ S, lu S * DS_ f g S :=
          Finset.single_le_sum (f := fun S => lu S * DS_ f g S)
            (fun S _ => mul_nonneg (by positivity) (DS_nonneg hf hg.1 S)) (Finset.mem_univ _)
  have : ENNReal.ofReal (η / N) ≤ Istar p f := by
    unfold Istar
    refine le_trans ?_ (le_iSup₂ (f := fun lam (_ : lam ∈ simplex K) =>
      ⨅ g ∈ alt p f, ENNReal.ofReal (Dlam lam f g)) lu hlu)
    exact le_iInf₂ fun g hg => ENNReal.ofReal_le_ofReal (key g hg)
  intro h0
  rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
  have : 0 < η / N := by positivity
  linarith

end MTPAux1i

namespace MTPAux1i
open RobustPrefLearn.MTP

noncomputable def aR {K : ℕ} (π : Policy K) (f : Pref K) (h : List (Step K)) : ℝ :=
  (pathProb π f h).toReal

noncomputable def llr {K : ℕ} (f g : Pref K) (h : List (Step K)) : ℝ :=
  (h.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2))).sum

/-- Expected number of displays of `S` before stopping. -/
noncomputable def Nexp {K : ℕ} (π : Policy K) (f : Pref K) (S : DS K) : ℝ≥0∞ := by
  classical
  exact ∑' t : ℕ, ∑ v : Fin t → Step K,
    (if survives π (toHist v) then pathProb π f (toHist v) * π.disp (toHist v) S else 0)

lemma disp_le_one {K : ℕ} (π : Policy K) (hπ : Admissible π) (h : List (Step K)) (S : DS K) :
    π.disp h S ≤ 1 := by
  rw [← hπ h]
  exact Finset.single_le_sum (f := fun S => π.disp h S) (fun _ _ => zero_le') (Finset.mem_univ S)

lemma f_le_one {K : ℕ} {p : ℝ} {f : Pref K} (hf : f ∈ (Mp p : Set (Pref K))) (S : DS K)
    (X : Fin K) : f S X ≤ 1 := by
  rw [← f_sum_univ hf S]
  exact Finset.single_le_sum (f := fun X => f S X) (fun X _ => f_nonneg hf S X)
    (Finset.mem_univ X)

lemma pathProb_le_one {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (h : List (Step K)) : pathProb π f h ≤ 1 := by
  induction h with
  | nil => simp [pathProb]
  | cons x h ih =>
    obtain ⟨S, X⟩ := x
    simp only [pathProb]
    calc pathProb π f h * π.disp h S * ENNReal.ofReal (f S X) ≤ 1 * 1 * 1 := by
          gcongr
          · exact disp_le_one π hπ h S
          · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (f_le_one hf S X)
      _ = 1 := by simp

lemma pathProb_ne_top {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (h : List (Step K)) : pathProb π f h ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (pathProb_le_one π hπ f hf h)

lemma aR_cons {K : ℕ} {p : ℝ} (π : Policy K) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K)))
    (S : DS K) (X : Fin K) (h : List (Step K)) :
    aR π f ((S, X) :: h) = aR π f h * (π.disp h S).toReal * f S X := by
  unfold aR
  simp only [pathProb]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (f_nonneg hf S X)]

lemma aR_nonneg {K : ℕ} (π : Policy K) (f : Pref K) (h : List (Step K)) : 0 ≤ aR π f h :=
  ENNReal.toReal_nonneg

lemma disp_toReal_sum {K : ℕ} (π : Policy K) (hπ : Admissible π) (h : List (Step K)) :
    ∑ S, (π.disp h S).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun S _ => ne_top_of_le_ne_top ENNReal.one_ne_top
    (disp_le_one π hπ h S)), hπ h, ENNReal.toReal_one]

lemma aR_pos {K : ℕ} {p : ℝ} (π : Policy K) (f g : Pref K) (hf : f ∈ (Mp p : Set (Pref K)))
    (hg : g ∈ (Mp p : Set (Pref K))) :
    ∀ h : List (Step K), 0 < aR π f h → 0 < aR π g h ∧ llr f g h = Real.log (aR π f h / aR π g h) := by
  intro h
  induction h with
  | nil =>
    intro _
    simp [aR, pathProb, llr]
  | cons x h ih =>
    intro hpos
    obtain ⟨S, X⟩ := x
    rw [aR_cons π f hf] at hpos
    have hd : 0 ≤ (π.disp h S).toReal := ENNReal.toReal_nonneg
    have ha := aR_nonneg π f h
    have hfX := f_nonneg hf S X
    have h1 : 0 < aR π f h := by
      rcases ha.lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at hpos; simp at hpos
    have h2 : 0 < (π.disp h S).toReal := by
      rcases hd.lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at hpos; simp at hpos
    have h3 : 0 < f S X := by
      rcases hfX.lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at hpos; simp at hpos
    have hXS : X ∈ S.1 := by
      by_contra hX; rw [(hf.1 S X).2 hX] at h3; exact lt_irrefl _ h3
    have hgX : 0 < g S X := (hg.1 S X).1 hXS
    obtain ⟨ihb, ihl⟩ := ih h1
    refine ⟨by rw [aR_cons π g hg]; positivity, ?_⟩
    rw [aR_cons π f hf, aR_cons π g hg]
    unfold llr at ihl ⊢
    simp only [List.map_cons, List.sum_cons]
    rw [ihl]
    rw [show aR π f h * (π.disp h S).toReal * f S X / (aR π g h * (π.disp h S).toReal * g S X) =
      (aR π f h / aR π g h) * (f S X / g S X) by field_simp]
    rw [Real.log_mul (by positivity) (by positivity)]
    ring

/-- One step of Wald's identity for the log-likelihood ratio. -/
lemma wald_step {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f g : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (w : List (Step K)) :
    ∑ x : Step K, aR π f (x :: w) * llr f g (x :: w) =
      aR π f w * llr f g w + aR π f w * ∑ S, (π.disp w S).toReal * DS_ f g S := by
  rw [Fintype.sum_prod_type]
  have : ∀ S : DS K, ∑ X : Fin K, aR π f ((S, X) :: w) * llr f g ((S, X) :: w) =
      aR π f w * (π.disp w S).toReal * llr f g w +
        aR π f w * ((π.disp w S).toReal * DS_ f g S) := by
    intro S
    simp only [aR_cons π f hf]
    unfold llr
    simp only [List.map_cons, List.sum_cons]
    rw [DS_eq_univ hf g S]
    have hs := f_sum_univ hf S
    calc ∑ X : Fin K, aR π f w * (π.disp w S).toReal * f S X *
          (Real.log (f S X / g S X) + (List.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2)) w).sum)
        = aR π f w * (π.disp w S).toReal *
            (List.map (fun x => Real.log (f x.1 x.2 / g x.1 x.2)) w).sum * ∑ X : Fin K, f S X +
          aR π f w * ((π.disp w S).toReal *
            ∑ X : Fin K, f S X * Real.log (f S X / g S X)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun X _ => ?_
          ring
      _ = _ := by rw [hs, mul_one]
  rw [Finset.sum_congr rfl fun S _ => this S, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, ← Finset.mul_sum, disp_toReal_sum π hπ w, mul_one]

open Classical in
lemma wald_key {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f g : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (t : ℕ) :
    (∑ v : Fin (t + 1) → Step K,
        if stopsAt π (toHist v) then aR π f (toHist v) * llr f g (toHist v) else 0) +
      (∑ v : Fin (t + 1) → Step K,
        if survives π (toHist v) then aR π f (toHist v) * llr f g (toHist v) else 0) =
      ∑ w : Fin t → Step K, if survives π (toHist w) then
        aR π f (toHist w) * llr f g (toHist w) +
          aR π f (toHist w) * ∑ S, (π.disp (toHist w) S).toReal * DS_ f g S else 0 := by
  rw [← Finset.sum_add_distrib]
  rw [← (Fin.snocEquiv (fun _ => Step K)).sum_comp]
  have hsn : ∀ i : Step K × (Fin t → Step K),
      (Fin.snocEquiv (fun _ => Step K)) i = (Fin.snoc i.2 i.1 : Fin (t + 1) → Step K) :=
    fun i => rfl
  simp only [hsn, MTPAux.toHist_snoc, MTPAux.stopsAt_cons, MTPAux.survives_cons]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hs : survives π (toHist w)
  · rw [if_pos hs, ← wald_step π hπ f g hf (toHist w)]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hst : π.stop (x :: toHist w) <;> simp [hs, hst]
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro x _
    simp [hs]

open Classical in
theorem wald {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f g : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (T : ℕ) :
    (∑ t ∈ Finset.range (T + 1), ∑ v : Fin t → Step K,
        if stopsAt π (toHist v) then aR π f (toHist v) * llr f g (toHist v) else 0) +
      (∑ v : Fin T → Step K,
        if survives π (toHist v) then aR π f (toHist v) * llr f g (toHist v) else 0) =
      ∑ t ∈ Finset.range T, ∑ v : Fin t → Step K, if survives π (toHist v) then
          aR π f (toHist v) * ∑ S, (π.disp (toHist v) S).toReal * DS_ f g S else 0 := by
  induction T with
  | zero =>
    rw [Finset.sum_range_one, ← Finset.sum_add_distrib, Fintype.sum_unique]
    simp [MTPAux.toHist_zero, llr]
  | succ T ih =>
    rw [Finset.sum_range_succ (fun t => ∑ v : Fin t → Step K,
        if stopsAt π (toHist v) then aR π f (toHist v) * llr f g (toHist v) else 0) (T + 1),
      add_assoc, wald_key π hπ f g hf T]
    rw [Finset.sum_range_succ (fun t => ∑ v : Fin t → Step K, if survives π (toHist v) then
          aR π f (toHist v) * ∑ S, (π.disp (toHist v) S).toReal * DS_ f g S else 0) T, ← ih,
      add_assoc, ← Finset.sum_add_distrib]
    congr 2
    funext w
    split_ifs <;> ring

end MTPAux1i

namespace MTPAux1i
open RobustPrefLearn.MTP

lemma toReal_partial (F : ℕ → ℝ≥0∞) (hF : ∑' t, F t ≠ ⊤) :
    Filter.Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), (F t).toReal) Filter.atTop
      (𝓝 (∑' t, F t).toReal) := by
  have h := (ENNReal.tendsto_nat_tsum F).comp (Filter.tendsto_add_atTop_nat 1)
  have h2 := (ENNReal.tendsto_toReal hF).comp h
  refine h2.congr fun T => ?_
  simp only [Function.comp]
  rw [ENNReal.toReal_sum]
  intro t _
  exact ne_top_of_le_ne_top hF (ENNReal.le_tsum t)

lemma toReal_inner {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (t : ℕ) (P : (Fin t → Step K) → Prop) [DecidablePred P] :
    (∑ v : Fin t → Step K, if P v then pathProb π f (toHist v) else 0).toReal =
      ∑ v : Fin t → Step K, if P v then aR π f (toHist v) else 0 := by
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp [aR]
  · intro v _
    split_ifs
    · exact pathProb_ne_top π hπ f hf _
    · simp

open Classical in
lemma sum_Nexp {K : ℕ} (π : Policy K) (hπ : Admissible π) (f : Pref K) :
    ∑ S, Nexp π f S = expTau π f := by
  unfold Nexp expTau probGT
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  congr 1
  funext t
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs
  · rw [← Finset.mul_sum, hπ, mul_one]
  · simp

lemma Nexp_ne_top {K : ℕ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hE : expTau π f ≠ ⊤) (S : DS K) : Nexp π f S ≠ ⊤ := by
  refine ne_top_of_le_ne_top hE ?_
  rw [← sum_Nexp π hπ f]
  exact Finset.single_le_sum (f := fun S => Nexp π f S) (fun _ _ => zero_le') (Finset.mem_univ S)

open Classical in
lemma Nexp_partial {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (hE : expTau π f ≠ ⊤) (S : DS K) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ v : Fin t → Step K,
      (if survives π (toHist v) then aR π f (toHist v) * (π.disp (toHist v) S).toReal else 0) ≤
      (Nexp π f S).toReal := by
  have hterm : ∀ t (v : Fin t → Step K),
      (if survives π (toHist v) then pathProb π f (toHist v) * π.disp (toHist v) S else 0) ≠ ⊤ := by
    intro t v
    split_ifs
    · exact ENNReal.mul_ne_top (pathProb_ne_top π hπ f hf _)
        (ne_top_of_le_ne_top ENNReal.one_ne_top (disp_le_one π hπ _ S))
    · simp
  have e : ∑ t ∈ Finset.range T, ∑ v : Fin t → Step K,
      (if survives π (toHist v) then aR π f (toHist v) * (π.disp (toHist v) S).toReal else 0) =
      (∑ t ∈ Finset.range T, ∑ v : Fin t → Step K,
        (if survives π (toHist v) then pathProb π f (toHist v) * π.disp (toHist v) S else 0)).toReal := by
    rw [ENNReal.toReal_sum (fun t _ => ENNReal.sum_ne_top.2 (fun v _ => hterm t v))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ENNReal.toReal_sum (fun v _ => hterm t v)]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp [aR, ENNReal.toReal_mul]
  rw [e]
  apply ENNReal.toReal_mono (Nexp_ne_top π hπ f hE S)
  unfold Nexp
  exact ENNReal.sum_le_tsum _

lemma kl_bound (δ A A' B B' : ℝ) (h0 : 0 < δ) (h1 : δ ≤ 1 / 2) (hA : A + A' = 1)
    (hB : B + B' = 1) (hA' : A' ≤ δ) (hBd : B ≤ δ) :
    kl δ (1 - δ) ≤ (Real.log ((1 - δ) / δ) + 1) * A + (Real.log (δ / (1 - δ)) + 1) * A' -
      (1 - δ) / δ * B - δ / (1 - δ) * B' := by
  have h1d : 0 < 1 - δ := by linarith
  have hL : Real.log (δ / (1 - δ)) = -Real.log ((1 - δ) / δ) := by
    rw [← Real.log_inv, inv_div]
  have hL0 : 0 ≤ Real.log ((1 - δ) / δ) := by
    apply Real.log_nonneg; rw [le_div_iff₀ h0]; linarith
  have hkl : kl δ (1 - δ) = (1 - 2 * δ) * Real.log ((1 - δ) / δ) := by
    unfold kl
    rw [show 1 - (1 - δ) = δ by ring, hL]
    ring
  rw [hkl, hL]
  set L := Real.log ((1 - δ) / δ)
  have hc : (1 - δ) / δ - δ / (1 - δ) ≥ 0 := by
    rw [ge_iff_le, sub_nonneg, div_le_div_iff₀ h1d h0]; nlinarith
  have key : 1 - δ / (1 - δ) - ((1 - δ) / δ - δ / (1 - δ)) * δ = 0 := by
    field_simp; ring
  have hB' : B' = 1 - B := by linarith
  have hA2 : A = 1 - A' := by linarith
  rw [hB', hA2]
  nlinarith [mul_nonneg hL0 (sub_nonneg.2 hA'), mul_nonneg hc (sub_nonneg.2 hBd)]

open Classical in
/-- The change-of-measure inequality for one alternative `g`. -/
theorem main_ineq {K : ℕ} (p : ℝ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (π : Policy K)
    (hacc : IsDeltaAccurate p δ π) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) (g : Pref K)
    (hg : g ∈ alt p f) (hE : expTau π f ≠ ⊤) :
    kl δ (1 - δ) ≤ ∑ S, DS_ f g S * (Nexp π f S).toReal := by
  have hπ := hacc.1
  have hgM := hg.1
  obtain ⟨hstopf, hwrongf⟩ := hacc.2 f hf
  obtain ⟨hstopg, hwrongg⟩ := hacc.2 g hgM
  set c1 := (1 - δ) / δ with hc1
  set c2 := δ / (1 - δ) with hc2
  have h1d : 0 < 1 - δ := by linarith
  have hc1p : 0 < c1 := div_pos h1d hδ0
  have hc2p : 0 < c2 := div_pos hδ0 h1d
  set W := ∑ S, DS_ f g S * (Nexp π f S).toReal with hW
  -- the four ENNReal families
  let C : (t : ℕ) → (Fin t → Step K) → Prop := fun t v => IsTop f (π.select (toHist v))
  let FA : ℕ → ℝ≥0∞ := fun t => ∑ v : Fin t → Step K,
    if stopsAt π (toHist v) ∧ C t v then pathProb π f (toHist v) else 0
  let FA' : ℕ → ℝ≥0∞ := fun t => ∑ v : Fin t → Step K,
    if stopsAt π (toHist v) ∧ ¬ C t v then pathProb π f (toHist v) else 0
  let FB : ℕ → ℝ≥0∞ := fun t => ∑ v : Fin t → Step K,
    if stopsAt π (toHist v) ∧ C t v then pathProb π g (toHist v) else 0
  let FB' : ℕ → ℝ≥0∞ := fun t => ∑ v : Fin t → Step K,
    if stopsAt π (toHist v) ∧ ¬ C t v then pathProb π g (toHist v) else 0
  have hsplit : ∀ (q : Pref K), (∑' t, ∑ v : Fin t → Step K,
      if stopsAt π (toHist v) ∧ C t v then pathProb π q (toHist v) else 0) +
      (∑' t, ∑ v : Fin t → Step K,
      if stopsAt π (toHist v) ∧ ¬ C t v then pathProb π q (toHist v) else 0) = probStop π q := by
    intro q
    unfold probStop
    rw [← ENNReal.tsum_add]
    congr 1; funext t
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h1 : stopsAt π (toHist v) <;> by_cases h2 : C t v <;> simp [h1, h2]
  have hAA := hsplit f
  have hBB := hsplit g
  rw [hstopf] at hAA
  rw [hstopg] at hBB
  have hAfin : ∑' t, FA t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← hAA]; exact le_self_add)
  have hA'fin : ∑' t, FA' t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← hAA]; exact le_add_self)
  have hBfin : ∑' t, FB t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← hBB]; exact le_self_add)
  have hB'fin : ∑' t, FB' t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← hBB]; exact le_add_self)
  -- real limits
  set A := (∑' t, FA t).toReal
  set A' := (∑' t, FA' t).toReal
  set B := (∑' t, FB t).toReal
  set B' := (∑' t, FB' t).toReal
  have hsumA : A + A' = 1 := by
    rw [← ENNReal.toReal_add hAfin hA'fin]; simp only [FA, FA']; rw [hAA]; simp
  have hsumB : B + B' = 1 := by
    rw [← ENNReal.toReal_add hBfin hB'fin]; simp only [FB, FB']; rw [hBB]; simp
  have hA'le : A' ≤ δ := by
    have : ∑' t, FA' t = probWrong π f := by
      unfold probWrong; rfl
    simp only [A']
    rw [this]
    calc (probWrong π f).toReal ≤ (ENNReal.ofReal δ).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hwrongf
      _ = δ := ENNReal.toReal_ofReal hδ0.le
  have hBle : B ≤ δ := by
    have : ∑' t, FB t ≤ probWrong π g := by
      unfold probWrong
      refine ENNReal.tsum_le_tsum fun t => Finset.sum_le_sum fun v _ => ?_
      by_cases h1 : stopsAt π (toHist v) ∧ C t v
      · rw [if_pos h1, if_pos ⟨h1.1, fun htg => hg.2 _ _ h1.2 htg rfl⟩]
      · rw [if_neg h1]; exact zero_le'
    calc B ≤ (probWrong π g).toReal :=
          ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwrongg) this
      _ ≤ (ENNReal.ofReal δ).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hwrongg
      _ = δ := ENNReal.toReal_ofReal hδ0.le
  -- finite-horizon inequality
  have hfin : ∀ T : ℕ,
      (Real.log c1 + 1) * (∑ t ∈ Finset.range (T + 1), (FA t).toReal) +
        (Real.log c2 + 1) * (∑ t ∈ Finset.range (T + 1), (FA' t).toReal) -
        c1 * (∑ t ∈ Finset.range (T + 1), (FB t).toReal) -
        c2 * (∑ t ∈ Finset.range (T + 1), (FB' t).toReal) ≤ W + (probGT π g T).toReal := by
    intro T
    simp only [FA, FA', FB, FB', toReal_inner π hπ f hf, toReal_inner π hπ g hgM]
    -- pointwise lower bound by `a·llr`
    have hpt : ∀ t (v : Fin t → Step K),
        (Real.log c1 + 1) * (if stopsAt π (toHist v) ∧ C t v then aR π f (toHist v) else 0) +
          (Real.log c2 + 1) * (if stopsAt π (toHist v) ∧ ¬ C t v then aR π f (toHist v) else 0) -
          c1 * (if stopsAt π (toHist v) ∧ C t v then aR π g (toHist v) else 0) -
          c2 * (if stopsAt π (toHist v) ∧ ¬ C t v then aR π g (toHist v) else 0) ≤
        if stopsAt π (toHist v) then aR π f (toHist v) * llr f g (toHist v) else 0 := by
      intro t v
      have hp := aR_pos π f g hf hgM (toHist v)
      by_cases h1 : stopsAt π (toHist v)
      · by_cases h2 : C t v
        · simp only [h1, h2, true_and, not_true_eq_false, and_false, if_true, if_false, mul_zero,
            sub_zero, add_zero]
          have := plog (aR π f (toHist v)) (aR π g (toHist v)) c1 (llr f g (toHist v))
            (aR_nonneg _ _ _) (aR_nonneg _ _ _) hc1p hp
          linarith
        · simp only [h1, h2, true_and, not_false_eq_true, and_true, and_false, if_true, if_false,
            mul_zero, sub_zero, zero_add]
          have := plog (aR π f (toHist v)) (aR π g (toHist v)) c2 (llr f g (toHist v))
            (aR_nonneg _ _ _) (aR_nonneg _ _ _) hc2p hp
          linarith
      · simp [h1]
    have hstp : (Real.log c1 + 1) * (∑ t ∈ Finset.range (T + 1), ∑ v : Fin t → Step K,
          if stopsAt π (toHist v) ∧ C t v then aR π f (toHist v) else 0) +
        (Real.log c2 + 1) * (∑ t ∈ Finset.range (T + 1), ∑ v : Fin t → Step K,
          if stopsAt π (toHist v) ∧ ¬ C t v then aR π f (toHist v) else 0) -
        c1 * (∑ t ∈ Finset.range (T + 1), ∑ v : Fin t → Step K,
          if stopsAt π (toHist v) ∧ C t v then aR π g (toHist v) else 0) -
        c2 * (∑ t ∈ Finset.range (T + 1), ∑ v : Fin t → Step K,
          if stopsAt π (toHist v) ∧ ¬ C t v then aR π g (toHist v) else 0) ≤
        ∑ t ∈ Finset.range (T + 1), ∑ v : Fin t → Step K,
          if stopsAt π (toHist v) then aR π f (toHist v) * llr f g (toHist v) else 0 := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun v _ => hpt t v
    have hwald := wald π hπ f g hf T
    -- survivors
    have hsur : -(probGT π g T).toReal ≤ ∑ v : Fin T → Step K,
        if survives π (toHist v) then aR π f (toHist v) * llr f g (toHist v) else 0 := by
      unfold probGT
      rw [toReal_inner π hπ g hgM T (fun v => survives π (toHist v)), ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun v _ => ?_
      split_ifs
      · have := plog (aR π f (toHist v)) (aR π g (toHist v)) 1 (llr f g (toHist v))
          (aR_nonneg _ _ _) (aR_nonneg _ _ _) one_pos (aR_pos π f g hf hgM (toHist v))
        simp only [Real.log_one, mul_zero, zero_add, one_mul] at this
        linarith [aR_nonneg π f (toHist v)]
      · simp
    -- the Wald right-hand side is at most `W`
    have hrhs : ∑ t ∈ Finset.range T, ∑ v : Fin t → Step K, (if survives π (toHist v) then
          aR π f (toHist v) * ∑ S, (π.disp (toHist v) S).toReal * DS_ f g S else 0) ≤ W := by
      have e : ∑ t ∈ Finset.range T, ∑ v : Fin t → Step K, (if survives π (toHist v) then
          aR π f (toHist v) * ∑ S, (π.disp (toHist v) S).toReal * DS_ f g S else 0) =
          ∑ S, DS_ f g S * ∑ t ∈ Finset.range T, ∑ v : Fin t → Step K,
            (if survives π (toHist v) then aR π f (toHist v) * (π.disp (toHist v) S).toReal
              else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs
        · refine Finset.sum_congr rfl fun S _ => ?_; ring
        · simp
      rw [e, hW]
      gcongr with S
      · exact DS_nonneg hf hgM S
      · exact Nexp_partial π hπ f hf hE S T
    linarith
  -- pass to the limit
  have hlim1 : Filter.Tendsto (fun T : ℕ =>
      (Real.log c1 + 1) * (∑ t ∈ Finset.range (T + 1), (FA t).toReal) +
        (Real.log c2 + 1) * (∑ t ∈ Finset.range (T + 1), (FA' t).toReal) -
        c1 * (∑ t ∈ Finset.range (T + 1), (FB t).toReal) -
        c2 * (∑ t ∈ Finset.range (T + 1), (FB' t).toReal)) Filter.atTop
      (𝓝 ((Real.log c1 + 1) * A + (Real.log c2 + 1) * A' - c1 * B - c2 * B')) :=
    ((((toReal_partial FA hAfin).const_mul _).add ((toReal_partial FA' hA'fin).const_mul _)).sub
      ((toReal_partial FB hBfin).const_mul _)).sub ((toReal_partial FB' hB'fin).const_mul _)
  have hlim2 : Filter.Tendsto (fun T : ℕ => W + (probGT π g T).toReal) Filter.atTop (𝓝 (W + 0)) := by
    apply Filter.Tendsto.const_add
    -- `P_g(τ > T) = 1 - P_g(τ ≤ T) → 0`
    let FS : ℕ → ℝ≥0∞ := fun s => ∑ v : Fin s → Step K,
      (if stopsAt π (toHist v) then pathProb π g (toHist v) else 0)
    have hFS : ∑' s, FS s = 1 := hstopg
    have hp := toReal_partial FS (by rw [hFS]; exact ENNReal.one_ne_top)
    rw [hFS, ENNReal.toReal_one] at hp
    have : ∀ T, (probGT π g T).toReal = 1 - ∑ t ∈ Finset.range (T + 1), (FS t).toReal := by
      intro T
      have h := MTPAux.partial_eq p π hπ g hgM T
      have hfin : ∀ t ∈ Finset.range (T + 1), FS t ≠ ⊤ := by
        intro t _
        exact ne_top_of_le_ne_top ENNReal.one_ne_top (by rw [← hFS]; exact ENNReal.le_tsum t)
      have hgt : probGT π g T ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
        (by rw [← h]; exact le_self_add)
      have := congrArg ENNReal.toReal h
      rw [ENNReal.toReal_add hgt (ENNReal.sum_ne_top.2 hfin), ENNReal.toReal_sum hfin,
        ENNReal.toReal_one] at this
      simp only [FS]
      linarith
    simp_rw [this]
    have := hp.const_sub 1
    simpa using this
  rw [add_zero] at hlim2
  have hlimit := le_of_tendsto_of_tendsto' hlim1 hlim2 hfin
  have := kl_bound δ A A' B B' hδ0 hδ hsumA hsumB hA'le hBle
  linarith

end MTPAux1i

namespace MTPAux6f
open RobustPrefLearn.MTP

lemma toHist_append {K t m : ℕ} (a : Fin t → Step K) (b : Fin m → Step K) :
    toHist (Fin.append a b) = toHist b ++ toHist a := by
  simp [toHist, List.ofFn_fin_append]

lemma survives_of_append {K : ℕ} (π : Policy K) (u h : List (Step K))
    (hs : survives π (u ++ h)) : survives π h := by
  intro j hj
  have := hs (u.length + j) (by simp; omega)
  rwa [List.drop_length_add_append] at this

lemma marg {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (h : List (Step K)) :
    ∀ m : ℕ, ∑ b : Fin m → Step K, pathProb π f (toHist b ++ h) = pathProb π f h := by
  intro m
  induction m with
  | zero => rw [Fintype.sum_unique]; simp [MTPAux.toHist_zero]
  | succ m ih =>
    rw [← (Fin.snocEquiv (fun _ => Step K)).sum_comp]
    have hsn : ∀ i : Step K × (Fin m → Step K),
        (Fin.snocEquiv (fun _ => Step K)) i = (Fin.snoc i.2 i.1 : Fin (m + 1) → Step K) :=
      fun i => rfl
    simp only [hsn, MTPAux.toHist_snoc, List.cons_append]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [← ih]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∀ x : Step K, pathProb π f (x :: (toHist b ++ h)) =
        pathProb π f (toHist b ++ h) * (π.disp (toHist b ++ h) x.1 * ENNReal.ofReal (f x.1 x.2)) := by
      intro x; obtain ⟨S, X⟩ := x; simp only [pathProb]; ring
    simp_rw [this, ← Finset.mul_sum, MTPAux.step_sum p π hπ f hf, mul_one]

open Classical in
/-- Mass surviving `m` further steps is at most `(1 - ε)` of the current mass, provided a
stopping path of probability at least `ε · P(h)` exists from every surviving history. -/
lemma decay {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (m : ℕ) (ε : ℝ≥0∞) (hεt : ε ≠ ⊤)
    (hgood : ∀ h : List (Step K), h ≠ [] → survives π h → ∃ b : Fin m → Step K,
      ¬ survives π (toHist b ++ h) ∧ ε * pathProb π f h ≤ pathProb π f (toHist b ++ h))
    (t : ℕ) (ht : 1 ≤ t) :
    probGT π f (t + m) ≤ (1 - ε) * probGT π f t := by
  unfold probGT
  rw [← (Fin.appendEquiv t m).sum_comp]
  have hap : ∀ c : (Fin t → Step K) × (Fin m → Step K),
      (Fin.appendEquiv t m) c = Fin.append c.1 c.2 := fun c => rfl
  simp only [hap, toHist_append]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases hs : survives π (toHist a)
  · rw [if_pos hs]
    have hne : toHist a ≠ [] := by
      intro e
      have := congrArg List.length e
      simp [toHist] at this; omega
    obtain ⟨b0, hb0, hε⟩ := hgood (toHist a) hne hs
    have hfin : pathProb π f (toHist a) ≠ ⊤ := MTPAux1i.pathProb_ne_top π hπ f hf (toHist a)
    have hsum : (∑ b : Fin m → Step K, if survives π (toHist b ++ toHist a) then
        pathProb π f (toHist b ++ toHist a) else 0) + ε * pathProb π f (toHist a) ≤
        pathProb π f (toHist a) := by
      rw [← Finset.add_sum_erase (f := fun b => if survives π (toHist b ++ toHist a) then
        pathProb π f (toHist b ++ toHist a) else 0) _ (Finset.mem_univ b0)]
      simp only [if_neg hb0, zero_add]
      calc (∑ b ∈ Finset.univ.erase b0, if survives π (toHist b ++ toHist a) then
            pathProb π f (toHist b ++ toHist a) else 0) + ε * pathProb π f (toHist a)
          ≤ (∑ b ∈ Finset.univ.erase b0, pathProb π f (toHist b ++ toHist a)) +
              pathProb π f (toHist b0 ++ toHist a) := by
            gcongr with b
            split_ifs <;> simp
        _ = pathProb π f (toHist a) := by
            rw [add_comm, Finset.add_sum_erase (f := fun b => pathProb π f (toHist b ++ toHist a))
              _ (Finset.mem_univ b0)]
            exact marg π hπ f hf (toHist a) m
    rw [ENNReal.sub_mul (fun _ _ => hfin), one_mul]
    exact ENNReal.le_sub_of_add_le_right (ENNReal.mul_ne_top hεt hfin) hsum
  · rw [if_neg hs, mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (fun h' => hs (survives_of_append π _ _ h'))]

lemma probGT_anti {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (t : ℕ) : probGT π f (t + 1) ≤ probGT π f t := by
  rw [← MTPAux.key_step p π hπ f hf t]
  exact le_add_self

lemma probGT_le_one {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (t : ℕ) : probGT π f t ≤ 1 := by
  rw [← MTPAux.partial_eq p π hπ f hf t]
  exact le_self_add

/-- Geometric decay of the survival probabilities implies `E[τ] < ∞`. -/
theorem expTau_lt_top {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (m : ℕ) (hm : 1 ≤ m) (r : ℝ≥0∞) (hr : r < 1)
    (hdec : ∀ t, 1 ≤ t → probGT π f (t + m) ≤ r * probGT π f t) : expTau π f < ⊤ := by
  have : NeZero m := ⟨by omega⟩
  -- `P(τ > 1 + k m + i) ≤ r^k`
  have hk : ∀ k : ℕ, probGT π f (1 + k * m) ≤ r ^ k := by
    intro k
    induction k with
    | zero => simpa using probGT_le_one π hπ f hf 1
    | succ k ih =>
      have := hdec (1 + k * m) (by omega)
      rw [show 1 + k * m + m = 1 + (k + 1) * m by ring] at this
      calc _ ≤ r * probGT π f (1 + k * m) := this
        _ ≤ r * r ^ k := by gcongr
        _ = r ^ (k + 1) := by ring
  have hanti : Antitone (fun t => probGT π f t) :=
    antitone_nat_of_succ_le (probGT_anti π hπ f hf)
  unfold expTau
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt (probGT_le_one π hπ f hf 0) ENNReal.one_lt_top, ?_⟩
  rw [← (Nat.divModEquiv m).symm.tsum_eq]
  calc ∑' c : ℕ × Fin m, probGT π f ((Nat.divModEquiv m).symm c + 1)
      ≤ ∑' c : ℕ × Fin m, r ^ c.1 := by
        refine ENNReal.tsum_le_tsum fun c => ?_
        simp only [Nat.divModEquiv_symm_apply]
        calc probGT π f (c.1 * m + c.2 + 1) ≤ probGT π f (1 + c.1 * m) := hanti (by omega)
          _ ≤ r ^ c.1 := hk c.1
    _ = ∑' k : ℕ, ∑' _ : Fin m, r ^ k := ENNReal.tsum_prod (f := fun k (_ : Fin m) => r ^ k)
    _ = ∑' k : ℕ, (m : ℝ≥0∞) * r ^ k := by
        congr 1; funext k; rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ = (m : ℝ≥0∞) * ∑' k : ℕ, r ^ k := ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top m) (tsum_geometric_lt_top.2 hr)

end MTPAux6f

namespace MTPAux6f
open RobustPrefLearn.MTP

lemma toHist_const {K m : ℕ} (y : Step K) :
    toHist (fun _ : Fin m => y) = List.replicate m y := by
  simp [toHist]

def Uset (K : ℕ) (hK : 2 ≤ K) : DS K := ⟨Finset.univ, by simp; omega⟩

lemma relRank_univ {K : ℕ} (hK : 2 ≤ K) (σ : Equiv.Perm (Fin K)) (X : Fin K) :
    relRank σ (Uset K hK) X = (σ X).val + 1 := by
  unfold relRank Uset
  simp only
  have : (Finset.univ.filter (fun k => σ k ≤ σ X)) =
      (Finset.univ.filter (fun i : Fin K => i.val < (σ X).val + 1)).map σ.symm.toEmbedding := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro h; exact ⟨σ k, by rw [Fin.le_def] at h; omega, by simp⟩
    · rintro ⟨i, hi, rfl⟩; rw [Fin.le_def]; simp; omega
  rw [this, Finset.card_map, Fin.card_filter_val_lt]
  have := (σ X).2
  omega

lemma log_oa_univ {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (σ : Equiv.Perm (Fin K)) (X : Fin K) :
    Real.log (oa p σ (Uset K hK) X) =
      Real.log ((1 - p) / (1 - p ^ K)) + ((σ X).val : ℝ) * Real.log p := by
  have hc : 0 < (1 - p) / (1 - p ^ K) := by
    have : p ^ K < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
    apply div_pos <;> linarith
  unfold oa
  rw [if_pos (by simp [Uset]), relRank_univ hK σ X, Nat.add_sub_cancel]
  have hcard : (Uset K hK).1.card = K := by simp [Uset]
  rw [hcard, Real.log_mul hc.ne' (pow_pos hp0 _).ne', Real.log_pow]

lemma loglik_rep {K : ℕ} (p : ℝ) (σ : Equiv.Perm (Fin K)) (m : ℕ) (y : Step K)
    (h : List (Step K)) :
    loglikOA p σ (List.replicate m y ++ h) =
      m * Real.log (oa p σ y.1 y.2) + loglikOA p σ h := by
  unfold loglikOA
  rw [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate, nsmul_eq_mul]

lemma mtp_disp_univ {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (S1 : DS K) (β : ℝ)
    (h : List (Step K)) (hh : h ≠ []) :
    ENNReal.ofReal (lamStar K p K / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) ≤
      (mtp p S1 β).disp h (Uset K hK) := by
  classical
  simp only [mtp, if_neg hh]
  set c := ENNReal.ofReal (lamStar K p K / ∑ m ∈ Finset.Icc 2 K, lamStar K p m)
  have hne := MTPAux.mle_nonempty p h
  have hcard : ((mle p h).card : ℝ≥0∞) ≠ 0 := by simpa using hne.ne_empty
  have hlow : ∀ σ ∈ mle p h, c ≤ ∑ n ∈ Finset.Icc 2 K,
      (if (Uset K hK).1 = topSet σ n then
        ENNReal.ofReal (lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) else 0) := by
    intro σ _
    have htop : (Uset K hK).1 = topSet σ K := by
      ext X; simp [Uset, topSet]
    calc c = (if (Uset K hK).1 = topSet σ K then
          ENNReal.ofReal (lamStar K p K / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) else 0) := by
            rw [if_pos htop]
      _ ≤ _ := Finset.single_le_sum (f := fun n => if (Uset K hK).1 = topSet σ n then
            ENNReal.ofReal (lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) else 0)
            (fun _ _ => zero_le') (Finset.mem_Icc.2 ⟨hK, le_rfl⟩)
  calc c = ((mle p h).card : ℝ≥0∞)⁻¹ * ∑ _σ ∈ mle p h, c := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hcard
          (ENNReal.natCast_ne_top _), one_mul]
    _ ≤ _ := by gcongr with σ hσ; exact hlow σ hσ

/-- On the path that shows `[K]` and votes for the top of an MLE ranking `m` times, MTP stops. -/
lemma stop_good {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (S1 : DS K) (β : ℝ) (h : List (Step K)) (σh : Equiv.Perm (Fin K)) (hσh : σh ∈ mle p h)
    (m : ℕ) (hm : 1 ≤ m) (hmβ : β ≤ m * Real.log (1 / p)) :
    (mtp p S1 β).stop (List.replicate m (Uset K hK, σh.symm 0) ++ h) := by
  classical
  set x0 := σh.symm 0
  have hlp : Real.log p < 0 := Real.log_neg hp0 hp1
  have hx0 : (σh x0).val = 0 := by simp [x0]
  have hLL : ∀ σ : Equiv.Perm (Fin K),
      loglikOA p σh (List.replicate m (Uset K hK, x0) ++ h) -
        loglikOA p σ (List.replicate m (Uset K hK, x0) ++ h) =
      (m : ℝ) * (-(((σ x0).val : ℝ) * Real.log p)) + (loglikOA p σh h - loglikOA p σ h) := by
    intro σ
    rw [loglik_rep, loglik_rep]
    simp only
    rw [log_oa_univ hK p hp0 hp1, log_oa_univ hK p hp0 hp1, hx0]
    push_cast; ring
  have hmle := (Finset.mem_filter.1 hσh).2
  refine ⟨by simp; omega, σh, ?_, ?_⟩
  · simp only [mle, Finset.mem_filter, Finset.mem_univ, true_and]
    intro σ
    have := hLL σ
    have h1 := hmle σ
    have h2 : 0 ≤ (m : ℝ) * (-(((σ x0).val : ℝ) * Real.log p)) := by
      apply mul_nonneg (by positivity)
      have : (0 : ℝ) ≤ ((σ x0).val : ℝ) := by positivity
      nlinarith
    linarith
  · intro σ' hd
    have hv : 1 ≤ (σ' x0).val := by have := hd x0 hx0; omega
    rw [hLL σ']
    have h1 := hmle σ'
    have hL : Real.log (1 / p) = -Real.log p := by rw [one_div, Real.log_inv]
    have hv' : (1 : ℝ) ≤ ((σ' x0).val : ℝ) := by exact_mod_cast hv
    have : (m : ℝ) * Real.log (1 / p) ≤ (m : ℝ) * (-(((σ' x0).val : ℝ) * Real.log p)) := by
      rw [hL]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    linarith

lemma path_good {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (S1 : DS K) (β : ℝ) (f : Pref K)
    (x0 : Fin K) (h : List (Step K)) (hh : h ≠ []) (q η : ℝ≥0∞)
    (hq : q = ENNReal.ofReal (lamStar K p K / ∑ m ∈ Finset.Icc 2 K, lamStar K p m))
    (hη : η ≤ ENNReal.ofReal (f (Uset K hK) x0)) :
    ∀ m : ℕ, (q * η) ^ m * pathProb (mtp p S1 β) f h ≤
      pathProb (mtp p S1 β) f (List.replicate m (Uset K hK, x0) ++ h) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append]
    simp only [pathProb]
    have hne : List.replicate m (Uset K hK, x0) ++ h ≠ [] := by simp [hh]
    have hd := mtp_disp_univ hK p S1 β _ hne
    rw [← hq] at hd
    calc (q * η) ^ (m + 1) * pathProb (mtp p S1 β) f h
        = ((q * η) ^ m * pathProb (mtp p S1 β) f h) * q * η := by ring
      _ ≤ pathProb (mtp p S1 β) f (List.replicate m (Uset K hK, x0) ++ h) *
          (mtp p S1 β).disp (List.replicate m (Uset K hK, x0) ++ h) (Uset K hK) *
          ENNReal.ofReal (f (Uset K hK) x0) := by gcongr

end MTPAux6f

namespace MTPAux10
open RobustPrefLearn.MTP

lemma rank_ge_one {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) (hX : X ∈ S.1) :
    1 ≤ relRank τ S X :=
  Finset.card_pos.2 ⟨X, Finset.mem_filter.2 ⟨hX, le_rfl⟩⟩

lemma rank_le_card {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) :
    relRank τ S X ≤ S.1.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma rank_strict {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X X' : Fin K)
    (hX' : X' ∈ S.1) (hlt : τ X < τ X') : relRank τ S X < relRank τ S X' := by
  unfold relRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨X', Finset.mem_filter.2 ⟨hX', le_rfl⟩, ?_⟩
    intro h
    exact absurd (Finset.mem_filter.1 h).2 (not_le.2 hlt)
  · intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hk.2.trans hlt.le⟩

lemma rank_lt_iff {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X X' : Fin K)
    (hX : X ∈ S.1) (hX' : X' ∈ S.1) : relRank τ S X < relRank τ S X' ↔ τ X < τ X' := by
  constructor
  · intro h
    by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with h' | h'
    · exact absurd (rank_strict τ S X' X hX h') (not_lt.2 h.le)
    · rw [τ.injective h'] at h; exact lt_irrefl _ h
  · exact rank_strict τ S X X' hX'

lemma rank_inj {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X X' : Fin K)
    (hX : X ∈ S.1) (hX' : X' ∈ S.1) (h : relRank τ S X = relRank τ S X') : X = X' := by
  by_contra hne
  rcases lt_or_gt_of_ne (fun e : τ X = τ X' => hne (τ.injective e)) with h1 | h1
  · exact absurd h (rank_strict τ S X X' hX' h1).ne
  · exact absurd h.symm (rank_strict τ S X' X hX h1).ne

/-- The rank map `S → Fin |S|`, `X ↦ τ(X|S) - 1`, is a bijection. -/
noncomputable def rankEquiv {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) : S.1 ≃ Fin S.1.card :=
  Equiv.ofBijective (fun x => ⟨relRank τ S x.1 - 1, by
      have := rank_le_card τ S x.1; have := rank_ge_one τ S x.1 x.2; omega⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp⟩
    intro x y hxy
    simp only [Fin.mk.injEq] at hxy
    have := rank_ge_one τ S x.1 x.2; have := rank_ge_one τ S y.1 y.2
    exact Subtype.ext (rank_inj τ S x.1 y.1 x.2 y.2 (by omega)))

lemma rankEquiv_val {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (x : S.1) :
    ((rankEquiv τ S x : Fin S.1.card) : ℕ) = relRank τ S x.1 - 1 := rfl

/-- Chain property of `p`-separability along consecutive ranks. -/
lemma psep_chain {K : ℕ} (p : ℝ) (hp0 : 0 < p) (f : Pref K) (σf : Equiv.Perm (Fin K))
    (hps : PSep p f σf) (hfnn : ∀ S X, 0 ≤ f S X) (S : DS K) :
    ∀ d : ℕ, ∀ i j : Fin K, i ∈ S.1 → j ∈ S.1 → relRank σf S i = relRank σf S j + d →
      f S i ≤ p ^ d * f S j := by
  intro d
  induction d with
  | zero =>
    intro i j hi hj h
    rw [rank_inj σf S i j hi hj (by simpa using h)]; simp
  | succ d ih =>
    intro i j hi hj h
    -- the element of rank `r(j) + d`
    have hlt : relRank σf S j + d - 1 < S.1.card := by
      have := rank_le_card σf S i; omega
    obtain ⟨m, hm⟩ := (rankEquiv σf S).surjective ⟨relRank σf S j + d - 1, hlt⟩
    have hmv := congrArg Fin.val hm
    rw [rankEquiv_val] at hmv
    simp only at hmv
    have hm1 := rank_ge_one σf S m.1 m.2
    have hj1 := rank_ge_one σf S j hj
    have hrm : relRank σf S m.1 = relRank σf S j + d := by omega
    have h1 : f S i ≤ p * f S m.1 :=
      hps S m.1 i m.2 hi ((rank_lt_iff σf S m.1 i m.2 hi).1 (by omega))
    have h2 := ih m.1 j m.2 hj hrm
    calc f S i ≤ p * f S m.1 := h1
      _ ≤ p * (p ^ d * f S j) := by gcongr
      _ = p ^ (d + 1) * f S j := by ring

/-- The supermartingale inequality: `∑_{X∈S} f(X|S) f^OA_σ(X|S)/f^OA_{σ_f}(X|S) ≤ 1`. -/
theorem ratio_sum_le_one {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K)) (hps : PSep p f σf)
    (σ : Equiv.Perm (Fin K)) (S : DS K) :
    ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X) ≤ 1 := by
  classical
  have hfnn : ∀ S X, 0 ≤ f S X := by
    intro S X
    by_cases hX : X ∈ S.1
    · exact ((hf.1 S X).1 hX).le
    · exact ((hf.1 S X).2 hX).ge
  set n := S.1.card
  have hc : 0 < (1 - p) / (1 - p ^ n) := by
    have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by have := S.2; omega)
    apply div_pos <;> linarith
  set rσ := fun X => relRank σ S X
  set rf := fun X => relRank σf S X
  have hratio : ∀ X ∈ S.1, oa p σ S X / oa p σf S X = p ^ (rσ X - 1) / p ^ (rf X - 1) := by
    intro X hX
    simp only [oa, if_pos hX, rσ, rf]
    rw [mul_div_mul_left _ _ hc.ne']
  -- move to the subtype
  let u : S.1 → ℝ := fun x => f S x.1 / p ^ (rf x.1 - 1)
  let w : S.1 → ℝ := fun x => p ^ (rf x.1 - 1)
  let π : Equiv.Perm S.1 := (rankEquiv σ S).trans (rankEquiv σf S).symm
  have hπ : ∀ x, rf (π x).1 = rσ x.1 := by
    intro x
    have h1 : rankEquiv σf S (π x) = rankEquiv σ S x := by simp [π]
    have h2 := congrArg Fin.val h1
    rw [rankEquiv_val, rankEquiv_val] at h2
    have := rank_ge_one σf S (π x).1 (π x).2
    have := rank_ge_one σ S x.1 x.2
    simp only [rf, rσ]; omega
  have hmono : Monovary u w := by
    intro i j hij
    simp only [w] at hij
    have hlt : rf j.1 - 1 < rf i.1 - 1 := (pow_lt_pow_iff_right_of_lt_one₀ hp0 hp1).1 hij
    have hi1 := rank_ge_one σf S i.1 i.2
    have hj1 := rank_ge_one σf S j.1 j.2
    have hch := psep_chain p hp0 f σf hps hfnn S (rf i.1 - rf j.1) i.1 j.1 i.2 j.2
      (by simp only [rf] at hlt ⊢; omega)
    simp only [u]
    rw [div_le_div_iff₀ (pow_pos hp0 _) (pow_pos hp0 _)]
    have e : rf i.1 - 1 = (rf j.1 - 1) + (rf i.1 - rf j.1) := by simp only [rf] at hlt ⊢; omega
    rw [e, pow_add]
    calc f S i.1 * p ^ (rf j.1 - 1) ≤ p ^ (rf i.1 - rf j.1) * f S j.1 * p ^ (rf j.1 - 1) := by
          gcongr
      _ = f S j.1 * (p ^ (rf j.1 - 1) * p ^ (rf i.1 - rf j.1)) := by ring
  have hre := hmono.sum_mul_comp_perm_le_sum_mul (σ := π)
  have hsum1 : ∑ x : S.1, u x * w x = 1 := by
    have : ∀ x : S.1, u x * w x = f S x.1 := by
      intro x; simp only [u, w]; field_simp
    simp_rw [this]
    rw [Finset.sum_coe_sort S.1 (fun X => f S X)]
    exact hf.2.1 S
  have hsum2 : ∑ x : S.1, u x * w (π x) = ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X) := by
    rw [← Finset.sum_coe_sort S.1]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [u, w, hπ x]
    rw [hratio x.1 x.2]
    ring
  rw [← hsum2, ← hsum1]
  exact hre

end MTPAux10

namespace MTPAux5
open RobustPrefLearn.MTP

/-- Rankings satisfying (A-3) for the same preference induce the same strict order. -/
lemma order_transfer {K : ℕ} (g : Pref K) (σ τ : Equiv.Perm (Fin K)) (hσ : Ranks g σ)
    (hτ : Ranks g τ) (X X' : Fin K) (hne : X ≠ X') : σ X < σ X' ↔ τ X < τ X' := by
  have hcard : 2 ≤ ({X, X'} : Finset (Fin K)).card := by rw [Finset.card_pair hne]
  set S : DS K := ⟨{X, X'}, hcard⟩
  have h1 : X ∈ S.1 := by simp [S]
  have h2 : X' ∈ S.1 := by simp [S]
  rw [← hσ S X X' h1 h2 hne, hτ S X X' h1 h2 hne]

lemma psep_transfer {K : ℕ} (p : ℝ) (g : Pref K) (σ τ : Equiv.Perm (Fin K)) (hσ : Ranks g σ)
    (hτ : Ranks g τ) (hps : PSep p g σ) : PSep p g τ := by
  intro S X X' hX hX' hlt
  have hne : X ≠ X' := fun e => by rw [e] at hlt; exact lt_irrefl _ hlt
  exact hps S X X' hX hX' ((order_transfer g σ τ hσ hτ X X' hne).2 hlt)

lemma psep_of_rank {K : ℕ} (p : ℝ) (g : Pref K) (τ : Equiv.Perm (Fin K))
    (hg : g ∈ MpRank p τ) : PSep p g τ := by
  obtain ⟨σ0, hR0, hP0⟩ := hg.1.2.2
  exact psep_transfer p g σ0 τ hR0 hg.2 hP0

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

lemma relRank_one {K : ℕ} (S : DS K) (X : Fin K) :
    relRank (1 : Equiv.Perm (Fin K)) S X = (S.1.filter (fun k => k ≤ X)).card := by
  unfold relRank
  congr 1

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

lemma relRank_hat {K : ℕ} (m : Fin K) (S : DS K) (X : Fin K) :
    relRank (sigmaHat m) S X =
      if X < m then (S.1.filter (fun k => k ≤ X)).card + (if m ∈ S.1 then 1 else 0)
      else if X = m then (if m ∈ S.1 then 1 else 0)
      else (S.1.filter (fun k => k ≤ X)).card := by
  unfold relRank
  simp only [Finset.card_filter]
  have key : ∀ k : Fin K, (if sigmaHat m k ≤ sigmaHat m X then 1 else 0 : ℕ) =
      if X < m then (if k ≤ X then 1 else 0) + (if k = m then 1 else 0)
      else if X = m then (if k = m then 1 else 0)
      else (if k ≤ X then 1 else 0) := by
    intro k
    simp only [Fin.le_def, hv m k, hv m X]
    simp only [Fin.lt_def, Fin.ext_iff]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  split_ifs <;> simp_all [Finset.sum_add_distrib, Finset.sum_ite_eq']

/-- Split a sum over `S ∋ k` into the parts before `k`, at `k` and after `k`. -/
lemma sum_split {K : ℕ} (S : Finset (Fin K)) (k : Fin K) (hk : k ∈ S) (F : Fin K → ℝ) :
    ∑ X ∈ S, F X = ∑ X ∈ S.filter (fun X => X < k), F X + F k +
      ∑ X ∈ S.filter (fun X => k < X), F X := by
  classical
  have : ∀ X, F X = (if X < k then F X else 0) + (if X = k then F X else 0) +
      (if k < X then F X else 0) := by
    intro X
    rcases lt_trichotomy X k with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.2 h.le]
  rw [Finset.sum_congr rfl (fun X _ => this X), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_filter, Finset.sum_filter, Finset.sum_ite_eq' S k F, if_pos hk]

end MTPAux5

namespace MTPAux4
open RobustPrefLearn.MTP

/-- The permutation of `S` sending `X` to the element whose `σ_k`-rank in `S` equals the
`σ̂_k`-rank of `X`. -/
noncomputable def piS {K : ℕ} (σk : Equiv.Perm (Fin K)) (k : Fin K) (S : DS K) : Equiv.Perm S.1 :=
  (MTPAux10.rankEquiv (sigmaHat k) S).trans (MTPAux10.rankEquiv σk S).symm

lemma rank_piS {K : ℕ} (σk : Equiv.Perm (Fin K)) (k : Fin K) (S : DS K) (x : S.1) :
    relRank σk S (piS σk k S x).1 = relRank (sigmaHat k) S x.1 := by
  have h1 : MTPAux10.rankEquiv σk S (piS σk k S x) = MTPAux10.rankEquiv (sigmaHat k) S x := by
    simp [piS]
  have h2 := congrArg Fin.val h1
  rw [MTPAux10.rankEquiv_val, MTPAux10.rankEquiv_val] at h2
  have := MTPAux10.rank_ge_one σk S _ (piS σk k S x).2
  have := MTPAux10.rank_ge_one (sigmaHat k) S _ x.2
  omega

/-- `σ_k` and `σ̂_k` order the pair `(π x, π x')` resp. `(x, x')` in the same way. -/
lemma lt_piS {K : ℕ} (σk : Equiv.Perm (Fin K)) (k : Fin K) (S : DS K) (x x' : S.1) :
    σk (piS σk k S x).1 < σk (piS σk k S x').1 ↔ sigmaHat k x.1 < sigmaHat k x'.1 := by
  rw [← MTPAux10.rank_lt_iff σk S _ _ (piS σk k S x).2 (piS σk k S x').2, rank_piS, rank_piS,
    MTPAux10.rank_lt_iff (sigmaHat k) S _ _ x.2 x'.2]

/-- The rearranged preference `f̂`. -/
noncomputable def fhat {K : ℕ} (σk : Equiv.Perm (Fin K)) (k : Fin K) (f : Pref K) : Pref K :=
  fun S X => if hX : X ∈ S.1 then f S (piS σk k S ⟨X, hX⟩).1 else 0

lemma fhat_mem {K : ℕ} (p : ℝ) (σk : Equiv.Perm (Fin K)) (k : Fin K) (f : Pref K)
    (hf : f ∈ MpRank p σk) : fhat σk k f ∈ MpRank p (sigmaHat k) := by
  classical
  have hps := MTPAux5.psep_of_rank p f σk hf
  have hR := hf.2
  have hRanks : Ranks (fhat σk k f) (sigmaHat k) := by
    intro S X X' hX hX' hne
    simp only [fhat, dif_pos hX, dif_pos hX']
    have hne' : (piS σk k S ⟨X, hX⟩).1 ≠ (piS σk k S ⟨X', hX'⟩).1 := by
      intro e
      apply hne
      have := (piS σk k S).injective (Subtype.ext e)
      exact congrArg Subtype.val this
    rw [hR S _ _ (piS σk k S ⟨X, hX⟩).2 (piS σk k S ⟨X', hX'⟩).2 hne', lt_piS]
  refine ⟨⟨fun S X => ⟨fun hX => ?_, fun hX => ?_⟩, fun S => ?_, sigmaHat k, hRanks, ?_⟩, hRanks⟩
  · simp only [fhat, dif_pos hX]; exact (hf.1.1 S _).1 (piS σk k S ⟨X, hX⟩).2
  · simp only [fhat, dif_neg hX]
  · rw [← Finset.sum_coe_sort S.1]
    have : ∀ x : S.1, fhat σk k f S x.1 = f S (piS σk k S x).1 := by
      intro x; simp only [fhat, dif_pos x.2]
    simp_rw [this]
    rw [Equiv.sum_comp (piS σk k S) (fun y : S.1 => f S y.1), Finset.sum_coe_sort S.1 (f S)]
    exact hf.1.2.1 S
  · intro S X X' hX hX' hlt
    simp only [fhat, dif_pos hX, dif_pos hX']
    exact hps S _ _ (piS σk k S ⟨X, hX⟩).2 (piS σk k S ⟨X', hX'⟩).2
      ((lt_piS σk k S ⟨X, hX⟩ ⟨X', hX'⟩).2 hlt)

/-- `σ̂_k` restricted to the versions other than `k` is the identity order. -/
lemma hat_lt_iff {K : ℕ} (k X X' : Fin K) (hX : X ≠ k) (hX' : X' ≠ k) :
    sigmaHat k X < sigmaHat k X' ↔ X < X' := by
  rw [Fin.lt_def, Fin.lt_def, MTPAux5.hv k X, MTPAux5.hv k X']
  have h1 : X.val ≠ k.val := fun e => hX (Fin.ext e)
  have h2 : X'.val ≠ k.val := fun e => hX' (Fin.ext e)
  split_ifs <;> omega

lemma piS_k {K : ℕ} (σk : Equiv.Perm (Fin K)) (k : Fin K) (hσk : (σk k).val = 0) (S : DS K)
    (hkS : k ∈ S.1) : (piS σk k S ⟨k, hkS⟩).1 = k := by
  have h := rank_piS σk k S ⟨k, hkS⟩
  have hk1 : relRank (sigmaHat k) S k = 1 := by
    unfold relRank
    rw [Finset.card_eq_one]
    refine ⟨k, ?_⟩
    ext a
    simp only [Finset.mem_filter, Finset.mem_singleton, Fin.le_def, MTPAux5.hv k a,
      MTPAux5.hv k k, lt_irrefl, if_false, if_true]
    constructor
    · rintro ⟨_, h⟩
      apply Fin.ext
      split_ifs at h with h1 h2 <;> omega
    · rintro rfl; simp [hkS]
  rw [hk1] at h
  -- the element of `σ_k`-rank `1` in `S` is `k`
  by_contra hne
  have hlt : σk k < σk (piS σk k S ⟨k, hkS⟩).1 := by
    rw [Fin.lt_def, hσk]
    have : σk (piS σk k S ⟨k, hkS⟩).1 ≠ σk k := fun e => hne (σk.injective e)
    have : (σk (piS σk k S ⟨k, hkS⟩).1).val ≠ (σk k).val := fun e => this (Fin.ext e)
    omega
  have := MTPAux10.rank_strict σk S k _ (piS σk k S ⟨k, hkS⟩).2 hlt
  have := MTPAux10.rank_ge_one σk S k hkS
  omega

lemma key_S {K : ℕ} (p : ℝ) (k : Fin K) (fstar : Pref K)
    (hfstar : fstar ∈ MpRank p (1 : Equiv.Perm (Fin K))) (σk : Equiv.Perm (Fin K))
    (hσk : (σk k).val = 0) (f : Pref K) (hf : f ∈ MpRank p σk) (S : DS K) :
    DS_ fstar (fhat σk k f) S ≤ DS_ fstar f S := by
  classical
  set π' : Equiv.Perm (Fin K) := Equiv.Perm.ofSubtype (piS σk k S) with hπ'
  have hπS : ∀ X (hX : X ∈ S.1), π' X = (piS σk k S ⟨X, hX⟩).1 := by
    intro X hX; rw [hπ', Equiv.Perm.ofSubtype_apply_of_mem _ hX]
  have hπout : ∀ X, X ∉ S.1 → π' X = X := by
    intro X hX; rw [hπ', Equiv.Perm.ofSubtype_apply_of_not_mem _ hX]
  have hπmem : ∀ X ∈ S.1, π' X ∈ S.1 := by
    intro X hX; rw [hπS X hX]; exact (piS σk k S ⟨X, hX⟩).2
  have hfh : ∀ X ∈ S.1, fhat σk k f S X = f S (π' X) := by
    intro X hX; simp only [fhat, dif_pos hX, hπS X hX]
  have hfpos : ∀ X ∈ S.1, 0 < f S X := fun X hX => (hf.1.1 S X).1 hX
  have hfspos : ∀ X ∈ S.1, 0 < fstar S X := fun X hX => (hfstar.1.1 S X).1 hX
  have hfhpos : ∀ X ∈ S.1, 0 < fhat σk k f S X := fun X hX => by
    rw [hfh X hX]; exact hfpos _ (hπmem X hX)
  -- reduce to the cross-entropy terms
  have hD : ∀ h : Pref K, (∀ X ∈ S.1, 0 < h S X) →
      DS_ fstar h S = ∑ X ∈ S.1, fstar S X * Real.log (fstar S X) -
        ∑ X ∈ S.1, fstar S X * Real.log (h S X) := by
    intro h hh
    unfold DS_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun X hX => ?_
    rw [Real.log_div (hfspos X hX).ne' (hh X hX).ne']; ring
  rw [hD _ hfhpos, hD _ hfpos]
  suffices hsuff : ∑ X ∈ S.1, fstar S X * Real.log (f S X) ≤
      ∑ X ∈ S.1, fstar S X * Real.log (fhat σk k f S X) by linarith
  -- the rearrangement on `S \ {k}`
  set s := S.1.erase k
  let u : Fin K → ℝ := fun X => fstar S X
  let g : Fin K → ℝ := fun X => Real.log (f S (π' X))
  have hmono : MonovaryOn u g s := by
    intro i hi j hj hij
    have hiS := Finset.mem_of_mem_erase hi
    have hjS := Finset.mem_of_mem_erase hj
    have hik := Finset.ne_of_mem_erase hi
    have hjk := Finset.ne_of_mem_erase hj
    simp only [g] at hij
    have hlt : f S (π' i) < f S (π' j) :=
      (Real.log_lt_log_iff (hfpos _ (hπmem i hiS)) (hfpos _ (hπmem j hjS))).1 hij
    rw [← hfh i hiS, ← hfh j hjS] at hlt
    have hne : i ≠ j := fun e => by rw [e] at hlt; exact lt_irrefl _ hlt
    have hRh := (fhat_mem p σk k f hf).2 S i j hiS hjS hne
    have h1 : ¬ sigmaHat k i < sigmaHat k j := fun h => absurd (hRh.2 h) (not_le.2 hlt)
    have h2 : sigmaHat k j < sigmaHat k i := by
      rcases lt_or_gt_of_ne (fun e : sigmaHat k i = sigmaHat k j => hne ((sigmaHat k).injective e))
        with h | h
      · exact absurd h h1
      · exact h
    have h3 : j < i := (hat_lt_iff k j i hjk hik).1 h2
    have := (hfstar.2 S j i hjS hiS hne.symm).2 (by simpa using h3)
    exact this
  have hsupp : {x | π'.symm x ≠ x} ⊆ (s : Set (Fin K)) := by
    intro x hx
    simp only [s, Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
    by_cases hxS : x ∈ S.1
    · refine ⟨hxS, fun e => hx ?_⟩
      subst e
      rw [Equiv.symm_apply_eq, hπS x hxS, piS_k σk x hσk S hxS]
    · exact absurd ((Equiv.symm_apply_eq π').2 (hπout x hxS).symm) hx
  have hre := hmono.sum_mul_comp_perm_le_sum_mul hsupp
  simp only [u, g, Equiv.apply_symm_apply] at hre
  -- add back the `k` term
  by_cases hkS : k ∈ S.1
  · rw [← Finset.sum_erase_add _ _ hkS, ← Finset.sum_erase_add _ _ hkS, hfh k hkS,
      hπS k hkS, piS_k σk k hσk S hkS]
    have : ∑ X ∈ s, fstar S X * Real.log (fhat σk k f S X) =
        ∑ X ∈ s, fstar S X * Real.log (f S (π' X)) :=
      Finset.sum_congr rfl fun X hX => by rw [hfh X (Finset.mem_of_mem_erase hX)]
    rw [this]
    linarith
  · have hs : s = S.1 := Finset.erase_eq_of_notMem hkS
    rw [← hs]
    have : ∑ X ∈ s, fstar S X * Real.log (fhat σk k f S X) =
        ∑ X ∈ s, fstar S X * Real.log (f S (π' X)) :=
      Finset.sum_congr rfl fun X hX => by rw [hfh X (Finset.mem_of_mem_erase hX)]
    rw [this]
    exact hre

end MTPAux4

namespace MTPAux6L
open RobustPrefLearn.MTP

/-- One-step weights `λ(S|h) f(X|S)`. -/
noncomputable def wt {K : ℕ} (π : Policy K) (f : Pref K) (h : List (Step K)) (x : Step K) : ℝ :=
  (π.disp h x.1).toReal * f x.1 x.2

lemma wt_nonneg {K : ℕ} {p : ℝ} (π : Policy K) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K)))
    (h : List (Step K)) (x : Step K) : 0 ≤ wt π f h x :=
  mul_nonneg ENNReal.toReal_nonneg (MTPAux1i.f_nonneg hf _ _)

lemma wt_sum {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (h : List (Step K)) : ∑ x : Step K, wt π f h x = 1 := by
  unfold wt
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, MTPAux1i.f_sum_univ hf, mul_one]
  exact MTPAux1i.disp_toReal_sum π hπ h

/-- Conditional mean of an increment `ξ` after the history `h`. -/
noncomputable def mu {K : ℕ} (π : Policy K) (f : Pref K) (ξ : Step K → ℝ) (h : List (Step K)) : ℝ :=
  ∑ x : Step K, wt π f h x * ξ x

noncomputable def Ssum {K : ℕ} (ξ : Step K → ℝ) (h : List (Step K)) : ℝ := (h.map ξ).sum

/-- The compensator `∑_{s < t} E[ξ_{s+1} | H_s]`. -/
noncomputable def Usum {K : ℕ} (π : Policy K) (f : Pref K) (ξ : Step K → ℝ) :
    List (Step K) → ℝ
  | [] => 0
  | x :: h => Usum π f ξ h + mu π f ξ h

lemma aR_cons' {K : ℕ} {p : ℝ} (π : Policy K) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K)))
    (x : Step K) (h : List (Step K)) :
    MTPAux1i.aR π f (x :: h) = MTPAux1i.aR π f h * wt π f h x := by
  obtain ⟨S, X⟩ := x
  rw [MTPAux1i.aR_cons π f hf]; unfold wt; ring

/-- `E[e^{-λ(ξ-μ)}] ≤ e^{4λ²M²}` for increments bounded by `M`. -/
lemma one_step {ι : Type*} [Fintype ι] (w ξ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (M l : ℝ) (hM : ∀ i, |ξ i| ≤ M) (hl : 0 ≤ l) (hlM : 2 * l * M ≤ 1) :
    ∑ i, w i * Real.exp (-l * (ξ i - ∑ j, w j * ξ j)) ≤ Real.exp (4 * l ^ 2 * M ^ 2) := by
  set m := ∑ j, w j * ξ j with hm
  have hmM : |m| ≤ M := by
    calc |m| ≤ ∑ j, |w j * ξ j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, w j * |ξ j| := by
          refine Finset.sum_congr rfl fun j _ => ?_; rw [abs_mul, abs_of_nonneg (hw j)]
      _ ≤ ∑ j, w j * M := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hM j) (hw j)
      _ = M := by rw [← Finset.sum_mul, hw1, one_mul]
  have hy : ∀ i, |-l * (ξ i - m)| ≤ 1 := by
    intro i
    rw [abs_mul, abs_neg, abs_of_nonneg hl]
    calc l * |ξ i - m| ≤ l * (2 * M) := by
          apply mul_le_mul_of_nonneg_left _ hl
          calc |ξ i - m| ≤ |ξ i| + |m| := abs_sub _ _
            _ ≤ 2 * M := by linarith [hM i]
      _ ≤ 1 := by linarith
  have hb : ∀ i, Real.exp (-l * (ξ i - m)) ≤ 1 + (-l * (ξ i - m)) + (-l * (ξ i - m)) ^ 2 := by
    intro i
    have := Real.abs_exp_sub_one_sub_id_le (hy i)
    have := le_abs_self (Real.exp (-l * (ξ i - m)) - 1 - (-l * (ξ i - m)))
    linarith
  have hsq : ∀ i, (-l * (ξ i - m)) ^ 2 ≤ 4 * l ^ 2 * M ^ 2 := by
    intro i
    have h1 : |ξ i - m| ≤ 2 * M := by
      calc |ξ i - m| ≤ |ξ i| + |m| := abs_sub _ _
        _ ≤ 2 * M := by linarith [hM i]
    have h2 : (ξ i - m) ^ 2 ≤ (2 * M) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg l]
  calc ∑ i, w i * Real.exp (-l * (ξ i - m))
      ≤ ∑ i, w i * (1 + (-l * (ξ i - m)) + 4 * l ^ 2 * M ^ 2) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw i)
        linarith [hb i, hsq i]
    _ = 1 + 4 * l ^ 2 * M ^ 2 := by
        have e : ∀ i, w i * (1 + (-l * (ξ i - m)) + 4 * l ^ 2 * M ^ 2) =
            w i * (1 + 4 * l ^ 2 * M ^ 2) - l * (w i * ξ i) + l * m * w i := by
          intro i; ring
        simp_rw [e]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
          ← Finset.mul_sum, hw1, ← hm]
        ring
    _ ≤ Real.exp (4 * l ^ 2 * M ^ 2) := by linarith [Real.add_one_le_exp (4 * l ^ 2 * M ^ 2)]

/-- Exponential moment bound for the compensated sum along histories. -/
theorem chernoff_mgf {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (ξ : Step K → ℝ) (M l : ℝ) (hM : ∀ x, |ξ x| ≤ M)
    (hl : 0 ≤ l) (hlM : 2 * l * M ≤ 1) (t : ℕ) :
    ∑ v : Fin t → Step K, MTPAux1i.aR π f (toHist v) *
        Real.exp (-l * (Ssum ξ (toHist v) - Usum π f ξ (toHist v))) ≤
      Real.exp (4 * l ^ 2 * M ^ 2 * t) := by
  induction t with
  | zero =>
    rw [Fintype.sum_unique]
    simp [MTPAux.toHist_zero, Ssum, Usum, MTPAux1i.aR, pathProb]
  | succ t ih =>
    rw [← (Fin.snocEquiv (fun _ => Step K)).sum_comp]
    have hsn : ∀ i : Step K × (Fin t → Step K),
        (Fin.snocEquiv (fun _ => Step K)) i = (Fin.snoc i.2 i.1 : Fin (t + 1) → Step K) :=
      fun i => rfl
    simp only [hsn, MTPAux.toHist_snoc]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hstep : ∀ w : Fin t → Step K,
        ∑ x : Step K, MTPAux1i.aR π f (x :: toHist w) *
          Real.exp (-l * (Ssum ξ (x :: toHist w) - Usum π f ξ (x :: toHist w))) ≤
        MTPAux1i.aR π f (toHist w) *
          Real.exp (-l * (Ssum ξ (toHist w) - Usum π f ξ (toHist w))) *
          Real.exp (4 * l ^ 2 * M ^ 2) := by
      intro w
      have e : ∀ x : Step K, MTPAux1i.aR π f (x :: toHist w) *
          Real.exp (-l * (Ssum ξ (x :: toHist w) - Usum π f ξ (x :: toHist w))) =
          MTPAux1i.aR π f (toHist w) *
            Real.exp (-l * (Ssum ξ (toHist w) - Usum π f ξ (toHist w))) *
            (wt π f (toHist w) x * Real.exp (-l * (ξ x - mu π f ξ (toHist w)))) := by
        intro x
        rw [aR_cons' π f hf]
        simp only [Ssum, Usum, List.map_cons, List.sum_cons]
        rw [show -l * (ξ x + (List.map ξ (toHist w)).sum - (Usum π f ξ (toHist w) +
            mu π f ξ (toHist w))) = -l * ((List.map ξ (toHist w)).sum - Usum π f ξ (toHist w)) +
            -l * (ξ x - mu π f ξ (toHist w)) by ring, Real.exp_add]
        ring
      simp_rw [e, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
      exact one_step (wt π f (toHist w)) ξ (wt_nonneg π f hf _) (wt_sum π hπ f hf _) M l hM hl hlM
    calc _ ≤ ∑ w : Fin t → Step K, MTPAux1i.aR π f (toHist w) *
          Real.exp (-l * (Ssum ξ (toHist w) - Usum π f ξ (toHist w))) *
          Real.exp (4 * l ^ 2 * M ^ 2) := Finset.sum_le_sum fun w _ => hstep w
      _ = (∑ w : Fin t → Step K, MTPAux1i.aR π f (toHist w) *
          Real.exp (-l * (Ssum ξ (toHist w) - Usum π f ξ (toHist w)))) *
          Real.exp (4 * l ^ 2 * M ^ 2) := by rw [Finset.sum_mul]
      _ ≤ Real.exp (4 * l ^ 2 * M ^ 2 * t) * Real.exp (4 * l ^ 2 * M ^ 2) := by
          gcongr
      _ = Real.exp (4 * l ^ 2 * M ^ 2 * ((t + 1 : ℕ) : ℝ)) := by
          rw [← Real.exp_add]; push_cast; ring_nf

/-- Chernoff bound: the probability that the compensated sum falls below `-a t`. -/
theorem chernoff {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (ξ : Step K → ℝ) (M l : ℝ) (hM : ∀ x, |ξ x| ≤ M)
    (hl : 0 ≤ l) (hlM : 2 * l * M ≤ 1) (a : ℝ) (t : ℕ) :
    ∑ v : Fin t → Step K, (if Ssum ξ (toHist v) - Usum π f ξ (toHist v) ≤ -a * t then
        MTPAux1i.aR π f (toHist v) else 0) ≤
      Real.exp ((-l * a + 4 * l ^ 2 * M ^ 2) * t) := by
  classical
  have hmgf := chernoff_mgf π hπ f hf ξ M l hM hl hlM t
  calc _ ≤ ∑ v : Fin t → Step K, MTPAux1i.aR π f (toHist v) *
        Real.exp (-l * (Ssum ξ (toHist v) - Usum π f ξ (toHist v))) * Real.exp (-l * a * t) := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs with h
        · have : 1 ≤ Real.exp (-l * (Ssum ξ (toHist v) - Usum π f ξ (toHist v))) *
              Real.exp (-l * a * t) := by
            rw [← Real.exp_add]
            apply Real.one_le_exp
            nlinarith
          have h0 := MTPAux1i.aR_nonneg π f (toHist v)
          calc MTPAux1i.aR π f (toHist v) = MTPAux1i.aR π f (toHist v) * 1 := (mul_one _).symm
            _ ≤ MTPAux1i.aR π f (toHist v) *
                (Real.exp (-l * (Ssum ξ (toHist v) - Usum π f ξ (toHist v))) *
                  Real.exp (-l * a * t)) := mul_le_mul_of_nonneg_left this h0
            _ = _ := by ring
        · exact mul_nonneg (mul_nonneg (MTPAux1i.aR_nonneg _ _ _) (Real.exp_pos _).le)
            (Real.exp_pos _).le
    _ = (∑ v : Fin t → Step K, MTPAux1i.aR π f (toHist v) *
        Real.exp (-l * (Ssum ξ (toHist v) - Usum π f ξ (toHist v)))) * Real.exp (-l * a * t) := by
        rw [Finset.sum_mul]
    _ ≤ Real.exp (4 * l ^ 2 * M ^ 2 * t) * Real.exp (-l * a * t) := by gcongr
    _ = _ := by rw [← Real.exp_add]; ring_nf

end MTPAux6L

namespace MTPAux6L
open RobustPrefLearn.MTP

/-- The log-likelihood increment of `f^OA_{σ_f}` against `f^OA_σ`. -/
noncomputable def xi {K : ℕ} (p : ℝ) (σf σ : Equiv.Perm (Fin K)) (x : Step K) : ℝ :=
  Real.log (oa p σf x.1 x.2) - Real.log (oa p σ x.1 x.2)

lemma oa_pos {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (τ : Equiv.Perm (Fin K)) (S : DS K)
    (X : Fin K) (hX : X ∈ S.1) : 0 < oa p τ S X := by
  unfold oa
  rw [if_pos hX]
  have : p ^ S.1.card < 1 := pow_lt_one₀ hp0.le hp1 (by have := S.2; omega)
  have : 0 < (1 - p) / (1 - p ^ S.1.card) := by apply div_pos <;> linarith
  positivity

lemma Ssum_xi {K : ℕ} (p : ℝ) (σf σ : Equiv.Perm (Fin K)) (h : List (Step K)) :
    Ssum (xi p σf σ) h = loglikOA p σf h - loglikOA p σ h := by
  unfold Ssum loglikOA xi
  induction h with
  | nil => simp
  | cons x h ih => simp only [List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; ring

lemma log_oa_mem {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (τ : Equiv.Perm (Fin K)) (S : DS K)
    (X : Fin K) (hX : X ∈ S.1) :
    Real.log (oa p τ S X) = Real.log ((1 - p) / (1 - p ^ S.1.card)) +
      ((relRank τ S X - 1 : ℕ) : ℝ) * Real.log p := by
  have hc : 0 < (1 - p) / (1 - p ^ S.1.card) := by
    have : p ^ S.1.card < 1 := pow_lt_one₀ hp0.le hp1 (by have := S.2; omega)
    apply div_pos <;> linarith
  unfold oa
  rw [if_pos hX, Real.log_mul hc.ne' (pow_pos hp0 _).ne', Real.log_pow]

lemma xi_mem {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σf σ : Equiv.Perm (Fin K))
    (S : DS K) (X : Fin K) (hX : X ∈ S.1) :
    xi p σf σ (S, X) = (((relRank σ S X : ℕ) : ℝ) - (relRank σf S X : ℕ)) *
      Real.log (1 / p) := by
  unfold xi
  simp only
  rw [log_oa_mem p hp0 hp1 σf S X hX, log_oa_mem p hp0 hp1 σ S X hX]
  have h1 := MTPAux10.rank_ge_one σf S X hX
  have h2 := MTPAux10.rank_ge_one σ S X hX
  rw [Nat.cast_sub h1, Nat.cast_sub h2, one_div, Real.log_inv]
  push_cast; ring

lemma xi_bound {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σf σ : Equiv.Perm (Fin K))
    (x : Step K) : |xi p σf σ x| ≤ K * Real.log (1 / p) := by
  have hL : 0 < Real.log (1 / p) := by
    apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1
  obtain ⟨S, X⟩ := x
  by_cases hX : X ∈ S.1
  · rw [xi_mem p hp0 hp1 σf σ S X hX, abs_mul, abs_of_pos hL]
    apply mul_le_mul_of_nonneg_right _ hL.le
    have h1 := MTPAux10.rank_ge_one σf S X hX
    have h2 := MTPAux10.rank_ge_one σ S X hX
    have h3 := MTPAux10.rank_le_card σf S X
    have h4 := MTPAux10.rank_le_card σ S X
    have h5 : S.1.card ≤ K := by
      calc S.1.card ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_le_univ _
        _ = K := by simp
    rw [abs_le]
    constructor
    · have : ((relRank σf S X : ℕ) : ℝ) ≤ K := by exact_mod_cast h3.trans h5
      have : (0 : ℝ) ≤ (relRank σ S X : ℕ) := by positivity
      linarith
    · have : ((relRank σ S X : ℕ) : ℝ) ≤ K := by exact_mod_cast h4.trans h5
      have : (0 : ℝ) ≤ (relRank σf S X : ℕ) := by positivity
      linarith
  · have : xi p σf σ (S, X) = 0 := by unfold xi; simp [oa, hX]
    rw [this, abs_zero]; positivity

/-- Expected increment given the display set `S`. -/
noncomputable def ES {K : ℕ} (p : ℝ) (f : Pref K) (σf σ : Equiv.Perm (Fin K)) (S : DS K) : ℝ :=
  ∑ X : Fin K, f S X * xi p σf σ (S, X)

lemma ES_eq {K : ℕ} (p : ℝ) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K)))
    (σf σ : Equiv.Perm (Fin K)) (S : DS K) :
    ES p f σf σ S = ∑ X ∈ S.1, f S X * xi p σf σ (S, X) := by
  unfold ES
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro X _ hX
  simp [(hf.1 S X).2 hX]

lemma ES_nonneg {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K)) (hPf : PSep p f σf)
    (σ : Equiv.Perm (Fin K)) (S : DS K) : 0 ≤ ES p f σf σ S := by
  rw [ES_eq p f hf]
  have hr := MTPAux10.ratio_sum_le_one p hp0 hp1 f hf σf hPf σ S
  have hpt : ∀ X ∈ S.1, -(f S X * xi p σf σ (S, X)) ≤ f S X * (oa p σ S X / oa p σf S X - 1) := by
    intro X hX
    have h1 := oa_pos p hp0 hp1 σ S X hX
    have h2 := oa_pos p hp0 hp1 σf S X hX
    have hl : Real.log (oa p σ S X / oa p σf S X) ≤ oa p σ S X / oa p σf S X - 1 :=
      Real.log_le_sub_one_of_pos (div_pos h1 h2)
    rw [Real.log_div h1.ne' h2.ne'] at hl
    unfold xi
    simp only
    have := (hf.1 S X).1 hX
    nlinarith
  have : ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X - 1) =
      ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X) - 1 := by
    have e : ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X - 1) =
        ∑ X ∈ S.1, f S X * (oa p σ S X / oa p σf S X) - ∑ X ∈ S.1, f S X := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun X _ => ?_; ring
    rw [e, hf.2.1 S]
  have h3 := Finset.sum_le_sum hpt
  rw [this, Finset.sum_neg_distrib] at h3
  have hES := ES_eq p f hf σf σ S
  linarith

lemma mu_eq {K : ℕ} (p : ℝ) (π : Policy K) (f : Pref K) (σf σ : Equiv.Perm (Fin K))
    (h : List (Step K)) :
    mu π f (xi p σf σ) h = ∑ S, (π.disp h S).toReal * ES p f σf σ S := by
  unfold mu wt ES
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  ring

lemma ES_univ_pos {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K)) (hPf : PSep p f σf)
    (σ : Equiv.Perm (Fin K)) (hne : σ ≠ σf) : 0 < ES p f σf σ (MTPAux6f.Uset K hK) := by
  set U := MTPAux6f.Uset K hK
  obtain ⟨X0, hX0⟩ : ∃ X0, σ X0 ≠ σf X0 := by
    by_contra h; push_neg at h; exact hne (Equiv.ext h)
  have hU : ∀ X, X ∈ U.1 := fun X => by simp [U, MTPAux6f.Uset]
  rw [ES_eq p f hf]
  have hr := MTPAux10.ratio_sum_le_one p hp0 hp1 f hf σf hPf σ U
  have hpt : ∀ X ∈ U.1, -(f U X * xi p σf σ (U, X)) ≤ f U X * (oa p σ U X / oa p σf U X - 1) := by
    intro X hX
    have h1 := oa_pos p hp0 hp1 σ U X hX
    have h2 := oa_pos p hp0 hp1 σf U X hX
    have hl : Real.log (oa p σ U X / oa p σf U X) ≤ oa p σ U X / oa p σf U X - 1 :=
      Real.log_le_sub_one_of_pos (div_pos h1 h2)
    rw [Real.log_div h1.ne' h2.ne'] at hl
    unfold xi
    simp only
    have := (hf.1 U X).1 hX
    nlinarith
  have hstrict : -(f U X0 * xi p σf σ (U, X0)) < f U X0 * (oa p σ U X0 / oa p σf U X0 - 1) := by
    have h1 := oa_pos p hp0 hp1 σ U X0 (hU X0)
    have h2 := oa_pos p hp0 hp1 σf U X0 (hU X0)
    have hne1 : oa p σ U X0 / oa p σf U X0 ≠ 1 := by
      intro e
      rw [div_eq_one_iff_eq h2.ne'] at e
      have e2 := congrArg Real.log e
      rw [MTPAux6f.log_oa_univ hK p hp0 hp1, MTPAux6f.log_oa_univ hK p hp0 hp1] at e2
      have hlp : Real.log p ≠ 0 := (Real.log_neg hp0 hp1).ne
      have : ((σ X0).val : ℝ) = (σf X0).val := by
        have := mul_right_cancel₀ hlp (by linarith : ((σ X0).val : ℝ) * Real.log p =
          ((σf X0).val : ℝ) * Real.log p)
        exact this
      exact hX0 (Fin.ext (by exact_mod_cast this))
    have hl : Real.log (oa p σ U X0 / oa p σf U X0) < oa p σ U X0 / oa p σf U X0 - 1 :=
      Real.log_lt_sub_one_of_pos (div_pos h1 h2) hne1
    rw [Real.log_div h1.ne' h2.ne'] at hl
    unfold xi
    simp only
    have := (hf.1 U X0).1 (hU X0)
    nlinarith
  have : ∑ X ∈ U.1, f U X * (oa p σ U X / oa p σf U X - 1) =
      ∑ X ∈ U.1, f U X * (oa p σ U X / oa p σf U X) - 1 := by
    have e : ∑ X ∈ U.1, f U X * (oa p σ U X / oa p σf U X - 1) =
        ∑ X ∈ U.1, f U X * (oa p σ U X / oa p σf U X) - ∑ X ∈ U.1, f U X := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun X _ => ?_; ring
    rw [e, hf.2.1 U]
  have h3 := Finset.sum_lt_sum (fun X hX => hpt X hX) ⟨X0, hU X0, hstrict⟩
  rw [this, Finset.sum_neg_distrib] at h3
  linarith

/-- Positive drift of every `σ ≠ σ_f` against `σ_f` under MTP. -/
lemma mu_mtp_lower {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (S1 : DS K) (β : ℝ) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K)))
    (σf : Equiv.Perm (Fin K)) (hPf : PSep p f σf) (σ : Equiv.Perm (Fin K))
    (h : List (Step K)) (hh : h ≠ []) :
    (lamStar K p K / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) * ES p f σf σ (MTPAux6f.Uset K hK) ≤
      mu (mtp p S1 β) f (xi p σf σ) h := by
  rw [mu_eq]
  set U := MTPAux6f.Uset K hK
  have hdU := MTPAux6f.mtp_disp_univ hK p S1 β h hh
  have hdne : (mtp p S1 β).disp h U ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (MTPAux1i.disp_le_one _ (MTPAux.mtp_admissible hK p hp0 hp1 S1 β) h U)
  have hq : lamStar K p K / ∑ m ∈ Finset.Icc 2 K, lamStar K p m ≤ ((mtp p S1 β).disp h U).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hdne]; exact hdU
  calc (lamStar K p K / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) * ES p f σf σ U
      ≤ ((mtp p S1 β).disp h U).toReal * ES p f σf σ U :=
        mul_le_mul_of_nonneg_right hq (ES_nonneg p hp0 hp1 f hf σf hPf σ U)
    _ ≤ ∑ S, ((mtp p S1 β).disp h S).toReal * ES p f σf σ S :=
        Finset.single_le_sum (f := fun S => ((mtp p S1 β).disp h S).toReal * ES p f σf σ S)
          (fun S _ => mul_nonneg ENNReal.toReal_nonneg (ES_nonneg p hp0 hp1 f hf σf hPf σ S))
          (Finset.mem_univ U)

end MTPAux6L

namespace MTPAux6L
open RobustPrefLearn.MTP

def mapDS {K : ℕ} (σ : Equiv.Perm (Fin K)) (S : DS K) : DS K :=
  ⟨S.1.map σ.toEmbedding, by rw [Finset.card_map]; exact S.2⟩

lemma relRank_trans {K : ℕ} (σ τ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) :
    relRank (σ.trans τ) S X = relRank τ (mapDS σ S) (σ X) := by
  unfold relRank mapDS
  simp only
  rw [Finset.filter_map, Finset.card_map]
  rfl

lemma relRank_map_one {K : ℕ} (σ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) :
    relRank σ S X = ((mapDS σ S).1.filter (fun j => j ≤ σ X)).card := by
  unfold relRank mapDS
  simp only
  rw [Finset.filter_map, Finset.card_map]
  rfl

lemma mem_mapDS {K : ℕ} (σ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) :
    σ X ∈ (mapDS σ S).1 ↔ X ∈ S.1 := by
  simp [mapDS]

lemma rank_one_of_top {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) (hX : X ∈ S.1)
    (h0 : (τ X).val = 0) : relRank τ S X = 1 := by
  unfold relRank
  rw [Finset.card_eq_one]
  refine ⟨X, ?_⟩
  ext Y
  simp only [Finset.mem_filter, Finset.mem_singleton, Fin.le_def, h0]
  constructor
  · rintro ⟨_, hY⟩
    exact τ.injective (Fin.ext (by omega))
  · rintro rfl; exact ⟨hX, by omega⟩

lemma rank_sum {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : DS K) (G : ℕ → ℝ) :
    ∑ X ∈ S.1, G (relRank τ S X) = ∑ j ∈ Finset.range S.1.card, G (j + 1) := by
  rw [← Finset.sum_coe_sort S.1]
  have : ∀ x : S.1, relRank τ S x.1 = (MTPAux10.rankEquiv τ S x).val + 1 := by
    intro x
    rw [MTPAux10.rankEquiv_val]
    have := MTPAux10.rank_ge_one τ S x.1 x.2
    omega
  simp_rw [this]
  rw [Equiv.sum_comp (MTPAux10.rankEquiv τ S) (fun j : Fin S.1.card => G (j.val + 1))]
  exact Fin.sum_univ_eq_sum_range (fun j => G (j + 1)) _

lemma sum_split' {K : ℕ} (τ : Equiv.Perm (Fin K)) (S : Finset (Fin K)) (k : Fin K) (hk : k ∈ S)
    (F : Fin K → ℝ) :
    ∑ X ∈ S, F X = ∑ X ∈ S.filter (fun X => τ X < τ k), F X + F k +
      ∑ X ∈ S.filter (fun X => τ k < τ X), F X := by
  classical
  have : ∀ X, F X = (if τ X < τ k then F X else 0) + (if X = k then F X else 0) +
      (if τ k < τ X then F X else 0) := by
    intro X
    rcases lt_trichotomy (τ X) (τ k) with h | h | h
    · have : X ≠ k := fun e => by rw [e] at h; exact lt_irrefl _ h
      simp [h, this, not_lt.2 h.le]
    · have := τ.injective h; subst this; simp
    · have : X ≠ k := fun e => by rw [e] at h; exact lt_irrefl _ h
      simp [h, this, not_lt.2 h.le]
  rw [Finset.sum_congr rfl (fun X _ => this X), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_filter, Finset.sum_filter, Finset.sum_ite_eq' S k F, if_pos hk]

/-- The key drift inequality: for `f ∈ M_p` with ranking `σ_f`, any `σ'` with top `k`, and any
display set `S ∋ k`, `E_f[ξ | S] ≥ 𝔞_i/𝔟_n`, `i = σ_f(k|S)`, `n = |S|`. -/
theorem drift_claim {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K)) (hRf : Ranks f σf)
    (hPf : PSep p f σf) (σ' : Equiv.Perm (Fin K)) (k : Fin K) (hk : (σ' k).val = 0)
    (S : DS K) (hkS : k ∈ S.1) :
    aSeq p (relRank σf S k) / bSeq p S.1.card ≤ ES p f σf σ' S := by
  classical
  set n := S.1.card with hn
  have hn2 : 2 ≤ n := S.2
  set r : Fin K → ℕ := fun X => relRank σf S X with hr
  set i := r k with hi
  have hr1 : ∀ X ∈ S.1, 1 ≤ r X := fun X hX => MTPAux10.rank_ge_one σf S X hX
  have hi1 : 1 ≤ i := hr1 k hkS
  have hin : i ≤ n := MTPAux10.rank_le_card σf S k
  have hL : 0 < Real.log (1 / p) := by
    apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1
  have hf1 := MTPAux1i.f_nonneg hf
  set m := σf k
  set σt : Equiv.Perm (Fin K) := σf.trans (sigmaHat m) with hσt
  -- ranks under `σ̃`
  have hrt : ∀ X ∈ S.1, (relRank σt S X : ℝ) =
      if σf X < m then (r X : ℝ) + 1 else if X = k then 1 else (r X : ℝ) := by
    intro X hX
    rw [hσt, relRank_trans, MTPAux5.relRank_hat, if_pos ((mem_mapDS σf S k).2 hkS)]
    have hrX : ((mapDS σf S).1.filter (fun j => j ≤ σf X)).card = r X := by
      rw [hr]; simp only; rw [relRank_map_one]
    rw [hrX]
    by_cases h1 : σf X < m
    · rw [if_pos h1, if_pos h1]; push_cast; ring
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : σf X = m
      · have : X = k := σf.injective h2
        rw [if_pos h2, if_pos this]; simp
      · have : X ≠ k := fun e => h2 (by rw [e])
        rw [if_neg h2, if_neg this]
  -- Step C1: rearrangement
  have hC1 : ∑ X ∈ S.1, f S X * (relRank σt S X : ℝ) ≤ ∑ X ∈ S.1, f S X * (relRank σ' S X : ℝ) := by
    let ρ : Equiv.Perm S.1 := (MTPAux10.rankEquiv σ' S).trans (MTPAux10.rankEquiv σt S).symm
    have hρ : ∀ x : S.1, relRank σt S (ρ x).1 = relRank σ' S x.1 := by
      intro x
      have h1 : MTPAux10.rankEquiv σt S (ρ x) = MTPAux10.rankEquiv σ' S x := by simp [ρ]
      have h2 := congrArg Fin.val h1
      rw [MTPAux10.rankEquiv_val, MTPAux10.rankEquiv_val] at h2
      have := MTPAux10.rank_ge_one σt S _ (ρ x).2
      have := MTPAux10.rank_ge_one σ' S _ x.2
      omega
    have hσtk : (σt k).val = 0 := by
      show ((sigmaHat m) (σf k)).val = 0
      rw [MTPAux5.hv]; simp [m]
    have hρk : (ρ ⟨k, hkS⟩).1 = k := by
      have h := hρ ⟨k, hkS⟩
      rw [rank_one_of_top σ' S k hkS hk, ← rank_one_of_top σt S k hkS hσtk] at h
      exact MTPAux10.rank_inj σt S _ _ (ρ ⟨k, hkS⟩).2 hkS h
    set ρ' : Equiv.Perm (Fin K) := Equiv.Perm.ofSubtype ρ
    have hρS : ∀ X (hX : X ∈ S.1), ρ' X = (ρ ⟨X, hX⟩).1 := by
      intro X hX; rw [Equiv.Perm.ofSubtype_apply_of_mem _ hX]
    have hρout : ∀ X, X ∉ S.1 → ρ' X = X := by
      intro X hX; rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hX]
    set s := S.1.erase k
    have hanti : AntivaryOn (fun X => f S X) (fun X => (relRank σt S X : ℝ)) s := by
      intro a ha b hb hab
      have haS := Finset.mem_of_mem_erase ha
      have hbS := Finset.mem_of_mem_erase hb
      have hak := Finset.ne_of_mem_erase ha
      have hbk := Finset.ne_of_mem_erase hb
      have h1 : relRank σt S a < relRank σt S b := by
        have : ((relRank σt S a : ℕ) : ℝ) < relRank σt S b := hab
        exact_mod_cast this
      have h2 : σt a < σt b := (MTPAux10.rank_lt_iff σt S a b haS hbS).1 h1
      have h3 : σf a < σf b := by
        have ha' : σf a ≠ m := fun e => hak (σf.injective e)
        have hb' : σf b ≠ m := fun e => hbk (σf.injective e)
        exact (MTPAux4.hat_lt_iff m (σf a) (σf b) ha' hb').1 h2
      have hne : a ≠ b := fun e => by rw [e] at h3; exact lt_irrefl _ h3
      exact (hRf S a b haS hbS hne).2 h3
    have hsupp : {x | ρ' x ≠ x} ⊆ (s : Set (Fin K)) := by
      intro x hx
      simp only [s, Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
      by_cases hxS : x ∈ S.1
      · refine ⟨hxS, fun e => hx ?_⟩
        subst e; rw [hρS x hxS, hρk]
      · exact absurd (hρout x hxS) hx
    have hre := hanti.sum_mul_le_sum_mul_comp_perm hsupp
    have hval : ∀ X ∈ S.1, (relRank σt S (ρ' X) : ℝ) = (relRank σ' S X : ℝ) := by
      intro X hX; rw [hρS X hX, hρ ⟨X, hX⟩]
    rw [← Finset.sum_erase_add _ _ hkS, ← Finset.sum_erase_add _ _ hkS]
    have e2 : ∑ X ∈ s, f S X * (relRank σ' S X : ℝ) = ∑ X ∈ s, f S X * (relRank σt S (ρ' X) : ℝ) :=
      Finset.sum_congr rfl fun X hX => by rw [hval X (Finset.mem_of_mem_erase hX)]
    have e3 : (relRank σt S k : ℝ) = (relRank σ' S k : ℝ) := by
      rw [rank_one_of_top σ' S k hkS hk, rank_one_of_top σt S k hkS hσtk]
    rw [e2, e3]
    linarith
  -- Step C2: `∑ f (r̃ - r) = A - (i-1) f_k`
  set A := ∑ X ∈ S.1.filter (fun X => σf X < m), f S X with hA
  set B := ∑ X ∈ S.1.filter (fun X => m < σf X), f S X with hB
  have hsumf : A + f S k + B = 1 := by
    rw [hA, hB, ← sum_split' σf S.1 k hkS (fun X => f S X)]; exact hf.2.1 S
  have hC2 : ∑ X ∈ S.1, f S X * (relRank σt S X : ℝ) - ∑ X ∈ S.1, f S X * (r X : ℝ) =
      A - ((i : ℝ) - 1) * f S k := by
    rw [← Finset.sum_sub_distrib, sum_split' σf S.1 k hkS]
    have e1 : ∑ X ∈ S.1.filter (fun X => σf X < m), (f S X * (relRank σt S X : ℝ) -
        f S X * (r X : ℝ)) = A := by
      rw [hA]; refine Finset.sum_congr rfl fun X hX => ?_
      obtain ⟨hXS, hXk⟩ := Finset.mem_filter.1 hX
      rw [hrt X hXS, if_pos hXk]; ring
    have e2 : ∑ X ∈ S.1.filter (fun X => m < σf X), (f S X * (relRank σt S X : ℝ) -
        f S X * (r X : ℝ)) = 0 := by
      apply Finset.sum_eq_zero; intro X hX
      obtain ⟨hXS, hXk⟩ := Finset.mem_filter.1 hX
      have : X ≠ k := fun e => by rw [e] at hXk; exact lt_irrefl _ hXk
      rw [hrt X hXS, if_neg (not_lt.2 hXk.le), if_neg this]; ring
    rw [e1, e2, hrt k hkS, if_neg (lt_irrefl _), if_pos rfl]
    ring
  -- Step C3: chain bounds
  set P := p ^ (i - 1) with hP
  have hlow : ∀ X ∈ S.1.filter (fun X => σf X < m), f S k * p ^ (r X - 1) ≤ P * f S X := by
    intro X hX
    obtain ⟨hXS, hXk⟩ := Finset.mem_filter.1 hX
    have hlt : r X < i := MTPAux10.rank_strict σf S X k hkS hXk
    have := MTPAux10.psep_chain p hp0 f σf hPf hf1 S (i - r X) k X hkS hXS (by
      show relRank σf S k = relRank σf S X + (i - r X); simp only [hi, hr] at hlt ⊢; omega)
    have hX1 := hr1 X hXS
    calc f S k * p ^ (r X - 1) ≤ p ^ (i - r X) * f S X * p ^ (r X - 1) := by gcongr
      _ = P * f S X := by
        rw [hP, show i - 1 = (i - r X) + (r X - 1) by omega, pow_add]; ring
  have hup : ∀ X ∈ S.1.filter (fun X => m < σf X), P * f S X ≤ f S k * p ^ (r X - 1) := by
    intro X hX
    obtain ⟨hXS, hXk⟩ := Finset.mem_filter.1 hX
    have hlt : i < r X := MTPAux10.rank_strict σf S k X hXS hXk
    have := MTPAux10.psep_chain p hp0 f σf hPf hf1 S (r X - i) X k hXS hkS (by
      show relRank σf S X = relRank σf S k + (r X - i); simp only [hi, hr] at hlt ⊢; omega)
    calc P * f S X ≤ P * (p ^ (r X - i) * f S k) := by gcongr
      _ = f S k * p ^ (r X - 1) := by
        rw [hP, show r X - 1 = (i - 1) + (r X - i) by omega, pow_add]; ring
  have hfilt_lt : ∀ X ∈ S.1, (σf X < m ↔ r X < i) := fun X hX =>
    (MTPAux10.rank_lt_iff σf S X k hX hkS).symm
  have hfilt_gt : ∀ X ∈ S.1, (m < σf X ↔ i < r X) := fun X hX =>
    (MTPAux10.rank_lt_iff σf S k X hkS hX).symm
  have h1p : 1 - p ≠ 0 := by linarith
  have hp1' : p - 1 ≠ 0 := by linarith
  have hSα : ∑ X ∈ S.1.filter (fun X => σf X < m), p ^ (r X - 1) = (1 - P) / (1 - p) := by
    rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl (fun X hX => by rw [if_congr (hfilt_lt X hX) rfl rfl])]
    rw [rank_sum σf S (fun j => if j < i then p ^ (j - 1) else 0)]
    rw [← Finset.sum_filter]
    have : (Finset.range n).filter (fun j => j + 1 < i) = Finset.range (i - 1) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this]
    simp only [Nat.add_sub_cancel]
    rw [geom_sum_eq hp1.ne, hP]
    field_simp; ring
  have htot : ∑ X ∈ S.1, p ^ (r X - 1) = (1 - p ^ n) / (1 - p) := by
    rw [rank_sum σf S (fun j => p ^ (j - 1))]
    simp only [Nat.add_sub_cancel]
    rw [geom_sum_eq hp1.ne]
    field_simp; ring
  have hpi : p ^ i = P * p := by rw [hP, ← pow_succ]; congr 1; omega
  have hSγ : ∑ X ∈ S.1.filter (fun X => m < σf X), p ^ (r X - 1) = (p ^ i - p ^ n) / (1 - p) := by
    have := sum_split' σf S.1 k hkS (fun X => p ^ (r X - 1))
    rw [htot, hSα] at this
    rw [hpi]
    field_simp at this ⊢
    simp only [← hi] at this
    linarith
  have hAlow : f S k * ((1 - P) / (1 - p)) ≤ P * A := by
    rw [← hSα, Finset.mul_sum, hA, Finset.mul_sum]
    exact Finset.sum_le_sum hlow
  have hBup : P * B ≤ f S k * ((p ^ i - p ^ n) / (1 - p)) := by
    rw [← hSγ, hB, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hup
  set κ := (1 - (i : ℝ) * p ^ (i - 1) + ((i : ℝ) - 1) * p ^ i) / (1 - p ^ n) with hκ
  have hpn : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
  have hPpos : 0 < P := pow_pos hp0 _
  have hgi : 0 ≤ 1 - (i : ℝ) * p ^ (i - 1) + ((i : ℝ) - 1) * p ^ i := by
    rcases (show i = 1 ∨ 2 ≤ i by omega) with h | h
    · rw [h]; simp
    · have := MTPAux7.g_pos p hp0 hp1 (i - 2)
      have e : i - 2 + 2 = i := by omega
      have e2 : i - 2 + 1 = i - 1 := by omega
      rw [e, e2] at this
      linarith
  have hκ0 : 0 ≤ κ := div_nonneg hgi (by linarith)
  have hκ1 : κ ≤ 1 := by
    rw [hκ, div_le_one (by linarith)]
    have hpn' : p ^ n ≤ p ^ i := pow_le_pow_of_le_one hp0.le hp1.le hin
    have : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    have hPle : P * p ≤ P := by nlinarith
    rw [hpi]
    nlinarith
  have hkey : (1 - P) / (1 - p) - ((i : ℝ) - 1) * P -
      κ * ((1 - P) / (1 - p) + P + (p ^ i - p ^ n) / (1 - p)) = 0 := by
    rw [hκ, hpi]
    have h1pn : 1 - p ^ n ≠ 0 := by linarith
    have hPi : p ^ (i - 1) = P := rfl
    rw [hPi]
    field_simp
    ring
  have hfk := hf1 S k
  have hmain : κ ≤ A - ((i : ℝ) - 1) * f S k := by
    have hB' : B = 1 - A - f S k := by linarith
    have e1 : 0 ≤ (1 - κ) * (P * A - f S k * ((1 - P) / (1 - p))) :=
      mul_nonneg (by linarith) (by linarith)
    have e2 : 0 ≤ κ * (f S k * ((p ^ i - p ^ n) / (1 - p)) - P * B) :=
      mul_nonneg hκ0 (by linarith)
    have e3 : P * (A - ((i : ℝ) - 1) * f S k - κ) =
        (1 - κ) * (P * A - f S k * ((1 - P) / (1 - p))) +
        κ * (f S k * ((p ^ i - p ^ n) / (1 - p)) - P * B) +
        f S k * ((1 - P) / (1 - p) - ((i : ℝ) - 1) * P -
          κ * ((1 - P) / (1 - p) + P + (p ^ i - p ^ n) / (1 - p))) := by
      rw [hB']; ring
    rw [hkey, mul_zero, add_zero] at e3
    have : 0 ≤ P * (A - ((i : ℝ) - 1) * f S k - κ) := by rw [e3]; linarith
    have := (mul_nonneg_iff_of_pos_left hPpos).1 this
    linarith
  -- conclusion
  have hES : ES p f σf σ' S = Real.log (1 / p) *
      (∑ X ∈ S.1, f S X * (relRank σ' S X : ℝ) - ∑ X ∈ S.1, f S X * (r X : ℝ)) := by
    rw [ES_eq p f hf, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun X hX => ?_
    rw [xi_mem p hp0 hp1 σf σ' S X hX]; simp only [hr]; ring
  rw [hES]
  calc aSeq p i / bSeq p n = Real.log (1 / p) * κ := by
        unfold aSeq bSeq; rw [hκ]; ring
    _ ≤ Real.log (1 / p) * (A - ((i : ℝ) - 1) * f S k) := by gcongr
    _ = Real.log (1 / p) * (∑ X ∈ S.1, f S X * (relRank σt S X : ℝ) -
          ∑ X ∈ S.1, f S X * (r X : ℝ)) := by rw [hC2]
    _ ≤ _ := by gcongr

end MTPAux6L

namespace MTPAux6L
open RobustPrefLearn.MTP

lemma inner_eval' {K : ℕ} (T : Finset (Fin K)) (hc : 2 ≤ T.card) (G : DS K → ℝ) :
    ∑ S : DS K, (if S.1 = T then G S else 0) = G ⟨T, hc⟩ := by
  classical
  have : ∀ S : DS K, (if S.1 = T then G S else 0) =
      (if S = ⟨T, hc⟩ then G ⟨T, hc⟩ else 0) := by
    intro S
    by_cases h : S = ⟨T, hc⟩
    · rw [if_pos (by rw [h]), if_pos h, h]
    · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg h]
  simp_rw [this]
  simp

/-- Drift of at least `u*` when the MLE is exactly `σ_f` (the display distribution is `λ^OA_*`
on the prefix sets of `σ_f`). -/
theorem mu_good {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (S1 : DS K) (β : ℝ) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K)))
    (σf : Equiv.Perm (Fin K)) (hRf : Ranks f σf) (hPf : PSep p f σf)
    (h : List (Step K)) (hh : h ≠ []) (hmle : mle p h = {σf})
    (σ' : Equiv.Perm (Fin K)) (hd : diffTop σf σ') :
    uStar K p ≤ mu (mtp p S1 β) f (xi p σf σ') h := by
  classical
  set Λ := ∑ m ∈ Finset.Icc 2 K, lamStar K p m with hΛ
  have hΛpos : 0 < Λ := MTPAux.lamStar_sum_pos K hK p hp0 hp1
  have hc : ∀ n ∈ Finset.Icc 2 K, 0 ≤ lamStar K p n / Λ := fun n hn =>
    div_nonneg (MTPAux.lamStar_nonneg K p hp0 hp1 n (Finset.mem_Icc.1 hn).1) hΛpos.le
  -- the display probabilities
  have hdisp : ∀ S : DS K, ((mtp p S1 β).disp h S).toReal =
      ∑ n ∈ Finset.Icc 2 K, (if S.1 = topSet σf n then lamStar K p n / Λ else 0) := by
    intro S
    simp only [mtp, if_neg hh, hmle, Finset.card_singleton, Nat.cast_one, inv_one, one_mul,
      Finset.sum_singleton]
    rw [ENNReal.toReal_sum (fun n _ => by split_ifs <;> simp)]
    refine Finset.sum_congr rfl fun n hn => ?_
    split_ifs
    · exact ENNReal.toReal_ofReal (hc n hn)
    · simp
  rw [mu_eq]
  simp_rw [hdisp, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hcard : ∀ n ∈ Finset.Icc 2 K, 2 ≤ (topSet σf n).card := by
    intro n hn
    rw [MTPAux.card_topSet σf n (Finset.mem_Icc.1 hn).2]; exact (Finset.mem_Icc.1 hn).1
  -- the top of `σ'`
  set k := σ'.symm ⟨0, by omega⟩ with hk
  have hk0 : (σ' k).val = 0 := by simp [hk]
  have hfk : (σf k).val ≠ 0 := fun e => hd k e hk0
  set M := (σf k).val + 1 with hM
  have hM2 : 2 ≤ M := by omega
  have hMK : M ≤ K := by have := (σf k).2; omega
  have hterm : ∀ n ∈ Finset.Icc 2 K,
      (if M ≤ n then aSeq p M / Λ * (lamStar K p n / bSeq p n) else 0) ≤
      ∑ S : DS K, (if S.1 = topSet σf n then lamStar K p n / Λ else 0) * ES p f σf σ' S := by
    intro n hn
    have e : ∀ S : DS K, (if S.1 = topSet σf n then lamStar K p n / Λ else 0) * ES p f σf σ' S =
        if S.1 = topSet σf n then lamStar K p n / Λ * ES p f σf σ' S else 0 := by
      intro S; split_ifs <;> simp
    simp_rw [e]
    rw [inner_eval' (topSet σf n) (hcard n hn) (fun S => lamStar K p n / Λ * ES p f σf σ' S)]
    by_cases hMn : M ≤ n
    · rw [if_pos hMn]
      have hkT : k ∈ topSet σf n := by simp [topSet]; omega
      have hdc := drift_claim p hp0 hp1 f hf σf hRf hPf σ' k hk0 ⟨topSet σf n, hcard n hn⟩ hkT
      have hrel : relRank σf ⟨topSet σf n, hcard n hn⟩ k = M := by
        rw [hM, ← MTPAux6f.relRank_univ hK σf k]
        unfold relRank
        congr 1
        ext Y
        simp only [topSet, MTPAux6f.Uset, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.le_def]
        omega
      rw [hrel, MTPAux.card_topSet σf n (Finset.mem_Icc.1 hn).2] at hdc
      have hb : 0 < bSeq p n := by
        unfold bSeq; have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega); linarith
      calc aSeq p M / Λ * (lamStar K p n / bSeq p n) =
            lamStar K p n / Λ * (aSeq p M / bSeq p n) := by ring
        _ ≤ lamStar K p n / Λ * ES p f σf σ' ⟨topSet σf n, hcard n hn⟩ :=
            mul_le_mul_of_nonneg_left hdc (hc n hn)
    · rw [if_neg hMn]
      exact mul_nonneg (hc n hn) (ES_nonneg p hp0 hp1 f hf σf hPf σ' _)
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [← Finset.sum_filter]
  have hfilt : (Finset.Icc 2 K).filter (fun n => M ≤ n) = Finset.Icc (K - (K - M)) K := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hfilt, ← Finset.mul_sum, MTPAux7.telescope K p hp0 hp1 (K - M) (by omega)]
  have e : K - (K - M) = M := by omega
  rw [e]
  have ha := MTPAux7.aSeq_pos p hp0 hp1 M hM2
  unfold uStar
  rw [← hΛ]
  apply le_of_eq
  field_simp

end MTPAux6L

namespace MTPAux6L
open RobustPrefLearn.MTP

/-- Probability (real) of a history event at time `t`. -/
noncomputable def PR {K : ℕ} (π : Policy K) (f : Pref K) (t : ℕ) (Q : List (Step K) → Prop)
    [DecidablePred Q] : ℝ :=
  ∑ v : Fin t → Step K, if Q (toHist v) then MTPAux1i.aR π f (toHist v) else 0

lemma PR_nonneg {K : ℕ} (π : Policy K) (f : Pref K) (t : ℕ) (Q : List (Step K) → Prop)
    [DecidablePred Q] : 0 ≤ PR π f t Q :=
  Finset.sum_nonneg fun v _ => by split_ifs <;> simp [MTPAux1i.aR_nonneg]

lemma PR_mono {K : ℕ} (π : Policy K) (f : Pref K) (t : ℕ) (Q Q' : List (Step K) → Prop)
    [DecidablePred Q] [DecidablePred Q'] (h : ∀ h, Q h → Q' h) : PR π f t Q ≤ PR π f t Q' := by
  unfold PR
  refine Finset.sum_le_sum fun v _ => ?_
  by_cases h1 : Q (toHist v)
  · rw [if_pos h1, if_pos (h _ h1)]
  · rw [if_neg h1]; split_ifs <;> simp [MTPAux1i.aR_nonneg]

lemma PR_or {K : ℕ} (π : Policy K) (f : Pref K) (t : ℕ) (Q Q' : List (Step K) → Prop)
    [DecidablePred Q] [DecidablePred Q'] :
    PR π f t (fun h => Q h ∨ Q' h) ≤ PR π f t Q + PR π f t Q' := by
  unfold PR
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  have := MTPAux1i.aR_nonneg π f (toHist v)
  by_cases h1 : Q (toHist v) <;> by_cases h2 : Q' (toHist v) <;> simp [h1, h2, this]

lemma PR_exists {K : ℕ} {ι : Type*} (π : Policy K) (f : Pref K) (t : ℕ) (s : Finset ι)
    (Q : ι → List (Step K) → Prop) [∀ i, DecidablePred (Q i)] :
    PR π f t (fun h => ∃ i ∈ s, Q i h) ≤ ∑ i ∈ s, PR π f t (Q i) := by
  classical
  unfold PR
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun v _ => ?_
  by_cases h1 : ∃ i ∈ s, Q i (toHist v)
  · rw [if_pos h1]
    obtain ⟨i, hi, hq⟩ := h1
    calc MTPAux1i.aR π f (toHist v) = (if Q i (toHist v) then MTPAux1i.aR π f (toHist v) else 0) := by
          rw [if_pos hq]
      _ ≤ _ := Finset.single_le_sum (f := fun i => if Q i (toHist v) then
            MTPAux1i.aR π f (toHist v) else 0)
            (fun j _ => by split_ifs <;> simp [MTPAux1i.aR_nonneg]) hi
  · rw [if_neg h1]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [MTPAux1i.aR_nonneg]

lemma PR_le_one {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (t : ℕ) (Q : List (Step K) → Prop) [DecidablePred Q] :
    PR π f t Q ≤ 1 := by
  have htot : ∑ v : Fin t → Step K, MTPAux1i.aR π f (toHist v) = 1 := by
    have := MTPAux6f.marg π hπ f hf [] t
    simp only [List.append_nil, pathProb] at this
    unfold MTPAux1i.aR
    rw [← ENNReal.toReal_sum (fun v _ => MTPAux1i.pathProb_ne_top π hπ f hf _), this]
    simp
  rw [← htot]
  unfold PR
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs <;> simp [MTPAux1i.aR_nonneg]

/-- Marginalisation: an event about the prefix of length `j`. -/
lemma PR_drop {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (Q : List (Step K) → Prop) [DecidablePred Q] (j : ℕ) :
    ∀ t, j ≤ t → PR π f t (fun h => Q (h.drop (t - j))) = PR π f j Q := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => simp [PR]
  | succ t ht ih =>
    unfold PR at ih ⊢
    rw [← ih]
    rw [← (Fin.snocEquiv (fun _ => Step K)).sum_comp]
    have hsn : ∀ i : Step K × (Fin t → Step K),
        (Fin.snocEquiv (fun _ => Step K)) i = (Fin.snoc i.2 i.1 : Fin (t + 1) → Step K) :=
      fun i => rfl
    simp only [hsn, MTPAux.toHist_snoc]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    have e : t + 1 - j = (t - j) + 1 := by omega
    simp only [e, List.drop_succ_cons]
    by_cases hq : Q ((toHist w).drop (t - j))
    · simp only [if_pos hq]
      simp_rw [aR_cons' π f hf, ← Finset.mul_sum, wt_sum π hπ f hf, mul_one]
    · simp [hq]

lemma Usum_drop {K : ℕ} (π : Policy K) (f : Pref K) (ξ : Step K → ℝ) :
    ∀ h : List (Step K), Usum π f ξ h =
      ∑ j ∈ Finset.range h.length, mu π f ξ (h.drop (h.length - j)) := by
  intro h
  induction h with
  | nil => simp [Usum]
  | cons x h ih =>
    simp only [Usum, List.length_cons]
    rw [Finset.sum_range_succ, ih]
    have hlast : (x :: h).drop (h.length + 1 - h.length) = h := by
      rw [show h.length + 1 - h.length = 1 by omega]; rfl
    rw [hlast]
    have : ∀ j ∈ Finset.range h.length, (x :: h).drop (h.length + 1 - j) = h.drop (h.length - j) := by
      intro j hj
      have : h.length + 1 - j = (h.length - j) + 1 := by
        have := Finset.mem_range.1 hj; omega
      rw [this, List.drop_succ_cons]
    rw [Finset.sum_congr rfl (fun j hj => by rw [this j hj] : ∀ j ∈ Finset.range h.length,
      mu π f ξ ((x :: h).drop (h.length + 1 - j)) = mu π f ξ (h.drop (h.length - j)))]

end MTPAux6L

namespace MTPAux6L
open RobustPrefLearn.MTP

/-- A history is *bad* if it is empty or its MLE set is not exactly `{σ_f}`. -/
def Bad {K : ℕ} (p : ℝ) (σf : Equiv.Perm (Fin K)) (h : List (Step K)) : Prop :=
  h = [] ∨ mle p h ≠ {σf}

lemma bad_imp {K : ℕ} [NeZero K] (p : ℝ) (σf : Equiv.Perm (Fin K)) (h : List (Step K))
    (hh : h ≠ []) (hb : mle p h ≠ {σf}) :
    ∃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin K))).erase σf, Ssum (xi p σf σ) h ≤ 0 := by
  classical
  by_cases hσf : σf ∈ mle p h
  · have : ∃ σ ∈ mle p h, σ ≠ σf := by
      by_contra hc
      push_neg at hc
      exact hb (Finset.eq_singleton_iff_unique_mem.2 ⟨hσf, hc⟩)
    obtain ⟨σ, hσ, hne⟩ := this
    refine ⟨σ, Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩, ?_⟩
    rw [Ssum_xi]
    have := (Finset.mem_filter.1 hσ).2 σf
    linarith
  · obtain ⟨σ, hσ⟩ := MTPAux.mle_nonempty p h
    have hne : σ ≠ σf := fun e => hσf (e ▸ hσ)
    refine ⟨σ, Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩, ?_⟩
    rw [Ssum_xi]
    have := (Finset.mem_filter.1 hσ).2 σf
    linarith

lemma mu_nonneg {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (π : Policy K) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K)) (hPf : PSep p f σf)
    (σ : Equiv.Perm (Fin K)) (h : List (Step K)) : 0 ≤ mu π f (xi p σf σ) h := by
  rw [mu_eq]
  exact Finset.sum_nonneg fun S _ => mul_nonneg ENNReal.toReal_nonneg
    (ES_nonneg p hp0 hp1 f hf σf hPf σ S)

lemma M_pos {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    0 < (K : ℝ) * Real.log (1 / p) := by
  have hL : 0 < Real.log (1 / p) := by
    apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1
  have : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  positivity

/-- Chernoff with the explicit choice of `λ`: rate `l a / 2` with `l = min (a/(8M²)) (1/(2M))`. -/
lemma chernoff' {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (ξ : Step K → ℝ) (M : ℝ) (hMpos : 0 < M)
    (hM : ∀ x, |ξ x| ≤ M) (a : ℝ) (ha : 0 < a) (t : ℕ) :
    PR π f t (fun h => Ssum ξ h - Usum π f ξ h ≤ -a * t) ≤
      Real.exp (-(min (a / (8 * M ^ 2)) (1 / (2 * M)) * a / 2) * t) := by
  set l := min (a / (8 * M ^ 2)) (1 / (2 * M)) with hl
  have hl0 : 0 ≤ l := le_min (by positivity) (by positivity)
  have hlM : 2 * l * M ≤ 1 := by
    have : l ≤ 1 / (2 * M) := min_le_right _ _
    calc 2 * l * M ≤ 2 * (1 / (2 * M)) * M := by gcongr
      _ = 1 := by field_simp
  have hla : 4 * l ^ 2 * M ^ 2 ≤ l * a / 2 := by
    have : l ≤ a / (8 * M ^ 2) := min_le_left _ _
    have h8 : l * (8 * M ^ 2) ≤ a := by rwa [le_div_iff₀ (by positivity)] at this
    nlinarith
  have := chernoff π hπ f hf ξ M l hM hl0 hlM a t
  unfold PR
  refine this.trans (Real.exp_le_exp.2 ?_)
  have ht : (0 : ℝ) ≤ t := by positivity
  nlinarith

open Classical in
/-- Exponential bound on the probability of a bad history, uniformly in `β` and `S₁`. -/
theorem bad_bound {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K))
    (hPf : PSep p f σf) :
    ∃ γ > 0, ∃ C ≥ 0, ∀ (S1 : DS K) (β : ℝ) (s : ℕ),
      PR (mtp p S1 β) f s (Bad p σf) ≤ C * Real.exp (-γ * s) := by
  classical
  set M := (K : ℝ) * Real.log (1 / p) with hMdef
  have hMpos : 0 < M := M_pos hK p hp0 hp1
  set q := lamStar K p K / ∑ m ∈ Finset.Icc 2 K, lamStar K p m with hq
  have hqpos : 0 < q := by
    apply div_pos _ (MTPAux.lamStar_sum_pos K hK p hp0 hp1)
    unfold lamStar
    rw [if_neg (lt_irrefl K)]
    have hb : 0 < bSeq p K := by
      unfold bSeq; have : p ^ K < 1 := pow_lt_one₀ hp0.le hp1 (by omega); linarith
    have := MTPAux.aSeq_pos p hp0 hp1 K hK
    positivity
  set U := MTPAux6f.Uset K hK
  have hne : ((Finset.univ : Finset (Equiv.Perm (Fin K))).erase σf).Nonempty := by
    refine ⟨σf * Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩, Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩⟩
    intro e
    have := congrArg (fun τ => τ ⟨0, by omega⟩) e
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at this
    have := σf.injective this
    simp [Fin.ext_iff] at this
  obtain ⟨σm, hσm, hmin⟩ := Finset.exists_min_image _ (fun σ => ES p f σf σ U) hne
  set c0 := q * ES p f σf σm U with hc0
  have hc0pos : 0 < c0 := mul_pos hqpos (ES_univ_pos hK p hp0 hp1 f hf σf hPf σm
    (Finset.ne_of_mem_erase hσm))
  set a := c0 / 2
  have ha : 0 < a := by positivity
  set γ := min (a / (8 * M ^ 2)) (1 / (2 * M)) * a / 2 with hγdef
  have hγ : 0 < γ := by
    have : 0 < min (a / (8 * M ^ 2)) (1 / (2 * M)) := lt_min (by positivity) (by positivity)
    positivity
  set N := (Fintype.card (Equiv.Perm (Fin K)) : ℝ)
  have hN1 : 1 ≤ N := by
    have : 1 ≤ Fintype.card (Equiv.Perm (Fin K)) := Fintype.card_pos
    show (1 : ℝ) ≤ (Fintype.card (Equiv.Perm (Fin K)) : ℝ)
    exact_mod_cast this
  refine ⟨γ, hγ, N * Real.exp (2 * γ), by positivity, fun S1 β s => ?_⟩
  have hπ := MTPAux.mtp_admissible hK p hp0 hp1 S1 β
  rcases (show s < 2 ∨ 2 ≤ s by omega) with hs | hs
  · calc PR (mtp p S1 β) f s (Bad p σf) ≤ 1 := PR_le_one _ hπ f hf s _
      _ ≤ N * Real.exp (2 * γ) * Real.exp (-γ * s) := by
        rw [mul_assoc, ← Real.exp_add]
        have : 0 ≤ 2 * γ + -γ * s := by
          have : (s : ℝ) ≤ 2 := by exact_mod_cast hs.le
          nlinarith
        have := Real.one_le_exp this
        nlinarith
  -- `s ≥ 2`
  have hUsum : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin K))).erase σf,
      ∀ h : List (Step K), h.length = s →
        c0 * ((s : ℝ) - 1) ≤ Usum (mtp p S1 β) f (xi p σf σ) h := by
    intro σ hσ h hlen
    rw [Usum_drop, hlen]
    have hmu : ∀ j ∈ Finset.range s, (if j = 0 then 0 else c0) ≤
        mu (mtp p S1 β) f (xi p σf σ) (h.drop (h.length - j)) := by
      intro j hj
      split_ifs with hj0
      · exact mu_nonneg p hp0 hp1 _ f hf σf hPf σ _
      · have hne' : h.drop (h.length - j) ≠ [] := by
          intro e
          have := congrArg List.length e
          simp at this
          have := Finset.mem_range.1 hj
          omega
        calc c0 ≤ q * ES p f σf σ U := by
              rw [hc0]; exact mul_le_mul_of_nonneg_left (hmin σ hσ) hqpos.le
          _ ≤ _ := mu_mtp_lower hK p hp0 hp1 S1 β f hf σf hPf σ _ hne'
    rw [hlen] at hmu
    calc c0 * ((s : ℝ) - 1) = ∑ j ∈ Finset.range s, (if j = 0 then 0 else c0) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
          have : ((Finset.range s).filter (fun j => ¬ j = 0)).card = s - 1 := by
            have : (Finset.range s).filter (fun j => ¬ j = 0) = (Finset.range s).erase 0 := by
              ext j; simp [and_comm]
            rw [this, Finset.card_erase_of_mem (by simp; omega), Finset.card_range]
          rw [this, Nat.cast_sub (by omega)]; push_cast; ring
      _ ≤ _ := Finset.sum_le_sum hmu
  calc PR (mtp p S1 β) f s (Bad p σf)
      ≤ PR (mtp p S1 β) f s (fun h => ∃ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin K))).erase σf,
          Ssum (xi p σf σ) h - Usum (mtp p S1 β) f (xi p σf σ) h ≤ -a * s) := by
        unfold PR
        refine Finset.sum_le_sum fun v _ => ?_
        by_cases hb : Bad p σf (toHist v)
        · rw [if_pos hb]
          have hlen : (toHist v).length = s := by simp [toHist]
          have hh : toHist v ≠ [] := by intro e; rw [e] at hlen; simp at hlen; omega
          have hb' : mle p (toHist v) ≠ {σf} := hb.resolve_left hh
          obtain ⟨σ, hσ, hS⟩ := bad_imp p σf (toHist v) hh hb'
          rw [if_pos ⟨σ, hσ, by
            have := hUsum σ hσ (toHist v) hlen
            have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
            have : a * s ≤ c0 * ((s : ℝ) - 1) := by
              simp only [a]; nlinarith
            linarith⟩]
        · rw [if_neg hb]; split_ifs <;> simp [MTPAux1i.aR_nonneg]
    _ ≤ ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin K))).erase σf,
          PR (mtp p S1 β) f s (fun h =>
            Ssum (xi p σf σ) h - Usum (mtp p S1 β) f (xi p σf σ) h ≤ -a * s) :=
        PR_exists _ f s _ _
    _ ≤ ∑ _σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin K))).erase σf, Real.exp (-γ * s) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        have := chernoff' (mtp p S1 β) hπ f hf (xi p σf σ) M hMpos
          (xi_bound p hp0 hp1 σf σ) a ha s
        rw [hγdef]; simpa [neg_mul] using this
    _ ≤ N * Real.exp (-γ * s) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        have := Finset.card_le_univ ((Finset.univ : Finset (Equiv.Perm (Fin K))).erase σf)
        show (((Finset.univ : Finset (Equiv.Perm (Fin K))).erase σf).card : ℝ) ≤
          (Fintype.card (Equiv.Perm (Fin K)) : ℝ)
        exact_mod_cast this
    _ ≤ N * Real.exp (2 * γ) * Real.exp (-γ * s) := by
        have h1 : 1 ≤ Real.exp (2 * γ) := Real.one_le_exp (by positivity)
        have h2 : 0 < Real.exp (-γ * s) := Real.exp_pos _
        have hN0 : 0 ≤ N := by linarith
        have h3 : 0 ≤ N * Real.exp (-γ * s) := mul_nonneg hN0 h2.le
        calc N * Real.exp (-γ * s) = N * Real.exp (-γ * s) * 1 := (mul_one _).symm
          _ ≤ N * Real.exp (-γ * s) * Real.exp (2 * γ) := mul_le_mul_of_nonneg_left h1 h3
          _ = _ := by ring

end MTPAux6L

namespace MTPAux6L
open RobustPrefLearn.MTP

/-- If every alternative with a different top is beaten by `β`, MTP stops. -/
lemma stop_of_Z {K : ℕ} [NeZero K] (p : ℝ) (S1 : DS K) (β : ℝ) (hβ : 0 < β)
    (σf : Equiv.Perm (Fin K)) (h : List (Step K)) (hh : h ≠ [])
    (hZ : ∀ σ', diffTop σf σ' → β ≤ Ssum (xi p σf σ') h) : (mtp p S1 β).stop h := by
  classical
  obtain ⟨σ, hσ⟩ := MTPAux.mle_nonempty p h
  have hmax := (Finset.mem_filter.1 hσ).2
  -- `σ` has the same top as `σ_f`
  have htop : ∀ X, (σf X).val = 0 → (σ X).val = 0 := by
    intro X hX
    by_contra hc
    have hd : diffTop σf σ := by
      intro Y hY
      have : Y = X := σf.injective (Fin.ext (by rw [hY, hX]))
      rw [this]; exact hc
    have := hZ σ hd
    rw [Ssum_xi] at this
    have := hmax σf
    linarith
  refine ⟨hh, σ, hσ, fun σ' hd => ?_⟩
  have hd' : diffTop σf σ' := by
    intro X hX
    exact hd X (htop X hX)
  have := hZ σ' hd'
  rw [Ssum_xi] at this
  have := hmax σf
  linarith

lemma mu_abs_le {K : ℕ} {p : ℝ} (π : Policy K) (hπ : Admissible π) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (ξ : Step K → ℝ) (M : ℝ) (hM : ∀ x, |ξ x| ≤ M)
    (h : List (Step K)) : -M ≤ mu π f ξ h := by
  unfold mu
  have : ∑ x : Step K, wt π f h x * (-M) ≤ ∑ x : Step K, wt π f h x * ξ x :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (neg_le_of_abs_le (hM x))
      (wt_nonneg π f hf h x)
  rw [← Finset.sum_mul, wt_sum π hπ f hf h] at this
  linarith

open Classical in
/-- The compensator of an alternative with a different top grows like `u* t`, except on bad
prefixes. -/
lemma usum_lower {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (S1 : DS K) (β : ℝ) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K)))
    (σf : Equiv.Perm (Fin K)) (hRf : Ranks f σf) (hPf : PSep p f σf)
    (σ' : Equiv.Perm (Fin K)) (hd : diffTop σf σ') (h : List (Step K)) :
    uStar K p * h.length - (uStar K p + K * Real.log (1 / p)) *
      ((Finset.range h.length).filter (fun j => Bad p σf (h.drop (h.length - j)))).card ≤
      Usum (mtp p S1 β) f (xi p σf σ') h := by
  have hπ := MTPAux.mtp_admissible hK p hp0 hp1 S1 β
  rw [Usum_drop]
  set u := uStar K p
  set M := (K : ℝ) * Real.log (1 / p)
  have hterm : ∀ j ∈ Finset.range h.length,
      u - (u + M) * (if Bad p σf (h.drop (h.length - j)) then 1 else 0) ≤
        mu (mtp p S1 β) f (xi p σf σ') (h.drop (h.length - j)) := by
    intro j _
    by_cases hb : Bad p σf (h.drop (h.length - j))
    · rw [if_pos hb, mul_one]
      have := mu_abs_le _ hπ f hf (xi p σf σ') M (xi_bound p hp0 hp1 σf σ') (h.drop (h.length - j))
      linarith
    · rw [if_neg hb, mul_zero, sub_zero]
      simp only [Bad, not_or, not_not] at hb
      exact mu_good hK p hp0 hp1 S1 β f hf σf hRf hPf _ hb.1 hb.2 σ' hd
  calc u * h.length - (u + M) *
        ((Finset.range h.length).filter (fun j => Bad p σf (h.drop (h.length - j)))).card
      = ∑ j ∈ Finset.range h.length,
          (u - (u + M) * (if Bad p σf (h.drop (h.length - j)) then 1 else 0)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum hterm

lemma geom_Ico (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (m t : ℕ) :
    ∑ j ∈ Finset.Ico m t, r ^ j ≤ r ^ m / (1 - r) := by
  rcases le_or_gt t m with h | h
  · rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]; positivity
  · rw [Finset.sum_Ico_eq_sum_range]
    simp_rw [pow_add]
    rw [← Finset.mul_sum, geom_sum_eq hr1.ne, div_eq_mul_one_div (r ^ m)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 _)
    have h1 : 0 < 1 - r := by linarith
    have e : (r ^ (t - m) - 1) / (r - 1) = (1 - r ^ (t - m)) / (1 - r) := by
      have : r - 1 ≠ 0 := by linarith
      have : 1 - r ≠ 0 := by linarith
      field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ h1.le
    have : 0 ≤ r ^ (t - m) := pow_nonneg hr0 _
    linarith

end MTPAux6L

namespace MTPAux6L
open RobustPrefLearn.MTP

lemma uStar_pos {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : 0 < uStar K p := by
  unfold uStar
  exact one_div_pos.2 (MTPAux.lamStar_sum_pos K hK p hp0 hp1)

open Classical in
/-- Survival probabilities beyond `(1+ε)β/u*` decay geometrically, uniformly in `β` and `S₁`. -/
theorem surv_bound {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K))
    (hRf : Ranks f σf) (hPf : PSep p f σf) (ε : ℝ) (hε : 0 < ε) :
    ∃ A1 A2 r1 r2 : ℝ, 0 ≤ A1 ∧ 0 ≤ A2 ∧ 0 ≤ r1 ∧ r1 < 1 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
      ∀ (S1 : DS K) (β : ℝ), 0 < β → ∀ t : ℕ, 1 ≤ t → (1 + ε) * β ≤ uStar K p * t →
        PR (mtp p S1 β) f t (survives (mtp p S1 β)) ≤ A1 * r1 ^ t + A2 * r2 ^ t := by
  obtain ⟨γ, hγ, C, hC, hbad⟩ := bad_bound hK p hp0 hp1 f hf σf hPf
  set u := uStar K p
  have hu := uStar_pos hK p hp0 hp1
  set M := (K : ℝ) * Real.log (1 / p)
  have hM := M_pos hK p hp0 hp1
  set a := u * ε / (2 * (1 + ε)) with ha_def
  have ha : 0 < a := by positivity
  set c := a / (u + M) with hc_def
  have hc : 0 < c := by positivity
  set γ1 := min (a / (8 * M ^ 2)) (1 / (2 * M)) * a / 2 with hγ1
  have hγ1pos : 0 < γ1 := by
    have : 0 < min (a / (8 * M ^ 2)) (1 / (2 * M)) := lt_min (by positivity) (by positivity)
    positivity
  set N := (Fintype.card (Equiv.Perm (Fin K)) : ℝ)
  have hN : 0 ≤ N := by positivity
  set ρ := Real.exp (-γ)
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.2 (by linarith)
  refine ⟨N, N * (C * Real.exp γ / (1 - ρ)), Real.exp (-γ1), Real.exp (-γ * c), hN,
    by have : 0 < 1 - ρ := by linarith
       positivity, (Real.exp_pos _).le, Real.exp_lt_one_iff.2 (by linarith),
    (Real.exp_pos _).le, Real.exp_lt_one_iff.2 (by nlinarith), ?_⟩
  intro S1 β hβ t ht hT
  have hπ := MTPAux.mtp_admissible hK p hp0 hp1 S1 β
  set π := mtp p S1 β
  set m0 := ⌊c * t⌋₊ with hm0
  set D := (Finset.univ : Finset (Equiv.Perm (Fin K))).filter (fun σ' => diffTop σf σ')
  -- pointwise decomposition of the survival event
  have hsplit : ∀ h : List (Step K), h.length = t → survives π h →
      ∃ σ' ∈ D, (Ssum (xi p σf σ') h - Usum π f (xi p σf σ') h ≤ -a * t ∨
        ∃ j ∈ Finset.Ico m0 t, Bad p σf (h.drop (t - j))) := by
    intro h hlen hs
    have hh : h ≠ [] := by intro e; rw [e] at hlen; simp at hlen; omega
    have hns : ¬ π.stop h := by simpa using hs 0 (Nat.zero_le _)
    have : ∃ σ', diffTop σf σ' ∧ Ssum (xi p σf σ') h < β := by
      by_contra hc'
      push_neg at hc'
      exact hns (stop_of_Z p S1 β hβ σf h hh hc')
    obtain ⟨σ', hd, hS⟩ := this
    refine ⟨σ', Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hcard : ((Finset.range h.length).filter (fun j => Bad p σf (h.drop (h.length - j)))).card
        ≤ m0 := by
      rw [hlen]
      calc _ ≤ (Finset.range m0).card := by
            apply Finset.card_le_card
            intro j hj
            obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
            rw [Finset.mem_range] at hj1 ⊢
            by_contra hjm
            exact h2 j (Finset.mem_Ico.2 ⟨by omega, hj1⟩) hj2
        _ = m0 := Finset.card_range m0
    have hU := usum_lower hK p hp0 hp1 S1 β f hf σf hRf hPf σ' hd h
    rw [hlen] at hU
    have hm0c : (m0 : ℝ) ≤ c * t := Nat.floor_le (by positivity)
    have hcard' : (((Finset.range h.length).filter
        (fun j => Bad p σf (h.drop (h.length - j)))).card : ℝ) ≤ c * t := by
      have : (((Finset.range h.length).filter
        (fun j => Bad p σf (h.drop (h.length - j)))).card : ℝ) ≤ m0 := by exact_mod_cast hcard
      linarith
    rw [hlen] at hcard'
    have hU2 : u * t - a * t ≤ Usum π f (xi p σf σ') h := by
      have : (u + M) * (((Finset.range t).filter
          (fun j => Bad p σf (h.drop (t - j)))).card : ℝ) ≤ (u + M) * (c * t) :=
        mul_le_mul_of_nonneg_left hcard' (by positivity)
      have hum : u + M ≠ 0 := by linarith
      have e : (u + M) * (c * t) = a * t := by rw [hc_def]; field_simp
      linarith
    have hkey : β ≤ u * t - 2 * a * t := by
      have e : u * t - 2 * a * t = u * t / (1 + ε) := by
        rw [ha_def]; field_simp; ring
      rw [e, le_div_iff₀ (by linarith)]; linarith
    linarith
  -- the probability bound
  have hE2 : PR π f t (fun h => ∃ j ∈ Finset.Ico m0 t, Bad p σf (h.drop (t - j))) ≤
      C * Real.exp γ / (1 - ρ) * Real.exp (-γ * c) ^ t := by
    calc _ ≤ ∑ j ∈ Finset.Ico m0 t, PR π f t (fun h => Bad p σf (h.drop (t - j))) :=
          PR_exists π f t _ _
      _ = ∑ j ∈ Finset.Ico m0 t, PR π f j (Bad p σf) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          exact PR_drop π hπ f hf (Bad p σf) j t (Finset.mem_Ico.1 hj).2.le
      _ ≤ ∑ j ∈ Finset.Ico m0 t, C * ρ ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := hbad S1 β j
          rw [show Real.exp (-γ * j) = ρ ^ j by rw [← Real.exp_nat_mul]; ring_nf] at this
          exact this
      _ = C * ∑ j ∈ Finset.Ico m0 t, ρ ^ j := by rw [Finset.mul_sum]
      _ ≤ C * (ρ ^ m0 / (1 - ρ)) := by
          gcongr; exact geom_Ico ρ hρ0 hρ1 m0 t
      _ ≤ C * (Real.exp γ * Real.exp (-γ * c) ^ t / (1 - ρ)) := by
          have hle : ρ ^ m0 ≤ Real.exp γ * Real.exp (-γ * c) ^ t := by
            rw [show ρ ^ m0 = Real.exp (-γ * m0) by rw [← Real.exp_nat_mul]; ring_nf,
              ← Real.exp_nat_mul, ← Real.exp_add]
            apply Real.exp_le_exp.2
            have : c * t < m0 + 1 := Nat.lt_floor_add_one _
            nlinarith
          have h1ρ : 0 < 1 - ρ := by linarith
          apply mul_le_mul_of_nonneg_left _ hC
          exact div_le_div_of_nonneg_right hle h1ρ.le
      _ = C * Real.exp γ / (1 - ρ) * Real.exp (-γ * c) ^ t := by ring
  have hE1 : ∀ σ', PR π f t (fun h => Ssum (xi p σf σ') h - Usum π f (xi p σf σ') h ≤ -a * t) ≤
      Real.exp (-γ1) ^ t := by
    intro σ'
    have := chernoff' π hπ f hf (xi p σf σ') M hM (xi_bound p hp0 hp1 σf σ') a ha t
    refine this.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, hγ1]; ring_nf
  calc PR π f t (survives π)
      ≤ PR π f t (fun h => ∃ σ' ∈ D, ((Ssum (xi p σf σ') h - Usum π f (xi p σf σ') h ≤ -a * t) ∨
          ∃ j ∈ Finset.Ico m0 t, Bad p σf (h.drop (t - j)))) := by
        unfold PR
        refine Finset.sum_le_sum fun v _ => ?_
        by_cases hs : survives π (toHist v)
        · rw [if_pos hs, if_pos (hsplit _ (by simp [toHist]) hs)]
        · rw [if_neg hs]; split_ifs <;> simp [MTPAux1i.aR_nonneg]
    _ ≤ ∑ σ' ∈ D, PR π f t (fun h => (Ssum (xi p σf σ') h - Usum π f (xi p σf σ') h ≤ -a * t) ∨
          ∃ j ∈ Finset.Ico m0 t, Bad p σf (h.drop (t - j))) := PR_exists π f t _ _
    _ ≤ ∑ σ' ∈ D, (Real.exp (-γ1) ^ t +
          C * Real.exp γ / (1 - ρ) * Real.exp (-γ * c) ^ t) := by
        refine Finset.sum_le_sum fun σ' _ => ?_
        exact (PR_or π f t _ _).trans (add_le_add (hE1 σ') hE2)
    _ ≤ N * (Real.exp (-γ1) ^ t + C * Real.exp γ / (1 - ρ) * Real.exp (-γ * c) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by
          have : 0 < 1 - ρ := by linarith
          positivity)
        have := Finset.card_le_univ D
        show ((D.card : ℕ) : ℝ) ≤ (Fintype.card (Equiv.Perm (Fin K)) : ℝ)
        exact_mod_cast this
    _ = _ := by ring

end MTPAux6L

namespace MTPAux6L
open RobustPrefLearn.MTP

/-- `I^OA_* ≤ u*` (weak duality with the dual certificate `µ*` of Lemma 8 and Lemma 9). -/
theorem IOA_le {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IOA (K := K) p ≤ ENNReal.ofReal (uStar K p) := by
  classical
  obtain ⟨hmu0, hmu1, hmuS⟩ := lemma_8 K hK p hp0 hp1
  rw [lemma_9 K hK p hp0 hp1]
  set F := (Finset.univ : Finset (Equiv.Perm (Fin K))).filter (fun σ => NotTopOne σ)
  have hoa1 := MTPAux7.oa_mem p hp0 hp1 (1 : Equiv.Perm (Fin K))
  unfold IOA
  refine (iInf₂_le (oa p (1 : Equiv.Perm (Fin K))) hoa1.1).trans ?_
  unfold Istar
  refine iSup₂_le fun lam hlam => ?_
  set I := ⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
    ENNReal.ofReal (Dlam lam (oa p (1 : Equiv.Perm (Fin K))) g)
  have halt : ∀ σ ∈ F, oa p σ ∈ alt p (oa p (1 : Equiv.Perm (Fin K))) := by
    intro σ hσ
    have hσm := MTPAux7.oa_mem p hp0 hp1 σ
    refine ⟨hσm.1, fun k k' hk hk' e => ?_⟩
    subst e
    have h1 := MTPAux1i.isTop_of_rank _ 1 hoa1.2 k hk
    have h2 := MTPAux1i.isTop_of_rank _ σ hσm.2 k hk'
    exact (Finset.mem_filter.1 hσ).2 k h2 (by simpa using h1)
  have hI : ∀ σ ∈ F, I ≤ ENNReal.ofReal (Dlam lam (oa p 1) (oa p σ)) := fun σ hσ =>
    iInf₂_le (oa p σ) (halt σ hσ)
  have hD0 : ∀ σ, 0 ≤ Dlam lam (oa p (1 : Equiv.Perm (Fin K))) (oa p σ) := by
    intro σ
    exact Finset.sum_nonneg fun S _ => mul_nonneg (hlam.1 S)
      (MTPAux1i.DS_nonneg hoa1.1 (MTPAux7.oa_mem p hp0 hp1 σ).1 S)
  calc I = (∑ σ ∈ F, ENNReal.ofReal (muStar K p σ)) * I := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun σ _ => hmu0 σ), hmu1, ENNReal.ofReal_one, one_mul]
    _ = ∑ σ ∈ F, ENNReal.ofReal (muStar K p σ) * I := Finset.sum_mul _ _ _
    _ ≤ ∑ σ ∈ F, ENNReal.ofReal (muStar K p σ) *
          ENNReal.ofReal (Dlam lam (oa p 1) (oa p σ)) := by
        gcongr with σ hσ; exact hI σ hσ
    _ = ENNReal.ofReal (∑ σ ∈ F, muStar K p σ * Dlam lam (oa p 1) (oa p σ)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun σ _ => mul_nonneg (hmu0 σ) (hD0 σ))]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [ENNReal.ofReal_mul (hmu0 σ)]
    _ ≤ ENNReal.ofReal (lStar K p) := by
        apply ENNReal.ofReal_le_ofReal
        have e : ∑ σ ∈ F, muStar K p σ * Dlam lam (oa p 1) (oa p σ) =
            ∑ S, lam S * ∑ σ ∈ F, DS_ (oa p 1) (oa p σ) S * muStar K p σ := by
          unfold Dlam
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun σ _ => ?_
          ring
        rw [e]
        calc ∑ S, lam S * ∑ σ ∈ F, DS_ (oa p 1) (oa p σ) S * muStar K p σ
            ≤ ∑ S, lam S * lStar K p :=
              Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hmuS S) (hlam.1 S)
          _ = lStar K p := by rw [← Finset.sum_mul, hlam.2, one_mul]

/-- The sample-complexity bound `E_f[τ] ≤ (1+ε) β / u* + D(ε)`, uniformly in `β` and `S₁`. -/
theorem expTau_bound {K : ℕ} [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K))
    (hRf : Ranks f σf) (hPf : PSep p f σf) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, ∀ (S1 : DS K) (β : ℝ), 0 < β →
      expTau (mtp p S1 β) f ≤ ENNReal.ofReal ((1 + ε) * β / uStar K p + D) := by
  classical
  obtain ⟨A1, A2, r1, r2, hA1, hA2, hr10, hr11, hr20, hr21, hsb⟩ :=
    surv_bound hK p hp0 hp1 f hf σf hRf hPf ε hε
  have hu := uStar_pos hK p hp0 hp1
  refine ⟨2 + A1 / (1 - r1) + A2 / (1 - r2), fun S1 β hβ => ?_⟩
  have hπ := MTPAux.mtp_admissible hK p hp0 hp1 S1 β
  set T := ⌈(1 + ε) * β / uStar K p⌉₊ + 1 with hT
  set g : ℕ → ℝ := fun t => (if t < T then 1 else 0) + A1 * r1 ^ t + A2 * r2 ^ t with hg
  have hg0 : ∀ t, 0 ≤ g t := fun t => by
    simp only [hg]; have := pow_nonneg hr10 t; have := pow_nonneg hr20 t
    split_ifs <;> positivity
  have hs_ind : Summable (fun t : ℕ => if t < T then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.range T)
    intro t ht; rw [Finset.mem_range] at ht; simp [ht]
  have hs1 : Summable (fun t : ℕ => A1 * r1 ^ t) :=
    (summable_geometric_of_lt_one hr10 hr11).mul_left A1
  have hs2 : Summable (fun t : ℕ => A2 * r2 ^ t) :=
    (summable_geometric_of_lt_one hr20 hr21).mul_left A2
  have hsg : Summable g := (hs_ind.add hs1).add hs2
  have hpt : ∀ t, probGT (mtp p S1 β) f t ≤ ENNReal.ofReal (g t) := by
    intro t
    have hfin : probGT (mtp p S1 β) f t ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (MTPAux6f.probGT_le_one _ hπ f hf t)
    have hPR : (probGT (mtp p S1 β) f t).toReal = PR (mtp p S1 β) f t (survives (mtp p S1 β)) := by
      unfold probGT PR
      exact MTPAux1i.toReal_inner _ hπ f hf t (fun v => survives (mtp p S1 β) (toHist v))
    rw [← ENNReal.ofReal_toReal hfin, hPR]
    apply ENNReal.ofReal_le_ofReal
    have h1 := pow_nonneg hr10 t
    have h2 := pow_nonneg hr20 t
    by_cases htT : t < T
    · have := PR_le_one _ hπ f hf t (survives (mtp p S1 β))
      simp only [hg, if_pos htT]
      nlinarith
    · have ht1 : 1 ≤ t := by omega
      have htb : (1 + ε) * β ≤ uStar K p * t := by
        have : (1 + ε) * β / uStar K p ≤ ⌈(1 + ε) * β / uStar K p⌉₊ := Nat.le_ceil _
        have h3 : (⌈(1 + ε) * β / uStar K p⌉₊ : ℝ) ≤ t := by
          have : ⌈(1 + ε) * β / uStar K p⌉₊ ≤ t := by omega
          exact_mod_cast this
        rw [div_le_iff₀ hu] at this
        nlinarith
      have := hsb S1 β hβ t ht1 htb
      simp only [hg, if_neg htT]
      linarith
  unfold expTau
  calc ∑' t, probGT (mtp p S1 β) f t ≤ ∑' t, ENNReal.ofReal (g t) := ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (∑' t, g t) := (ENNReal.ofReal_tsum_of_nonneg hg0 hsg).symm
    _ ≤ ENNReal.ofReal ((1 + ε) * β / uStar K p + (2 + A1 / (1 - r1) + A2 / (1 - r2))) := by
        apply ENNReal.ofReal_le_ofReal
        have e1 : ∑' t : ℕ, (if t < T then (1 : ℝ) else 0) = T := by
          rw [tsum_eq_sum (s := Finset.range T) (fun t ht => by
            rw [Finset.mem_range] at ht; simp [ht])]
          rw [Finset.sum_ite_of_true (fun t ht => Finset.mem_range.1 ht)]
          simp
        have e2 : ∑' t : ℕ, A1 * r1 ^ t = A1 / (1 - r1) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr10 hr11, div_eq_mul_inv]
        have e3 : ∑' t : ℕ, A2 * r2 ^ t = A2 / (1 - r2) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr20 hr21, div_eq_mul_inv]
        rw [show (∑' t, g t) = (∑' t : ℕ, (if t < T then (1 : ℝ) else 0)) +
            ∑' t : ℕ, A1 * r1 ^ t + ∑' t : ℕ, A2 * r2 ^ t by
          simp only [hg]
          rw [(hs_ind.add hs1).tsum_add hs2, hs_ind.tsum_add hs1]]
        rw [e1, e2, e3]
        have hTle : (T : ℝ) ≤ (1 + ε) * β / uStar K p + 2 := by
          have hc := Nat.ceil_lt_add_one (show 0 ≤ (1 + ε) * β / uStar K p by positivity)
          rw [hT]; push_cast; linarith
        linarith

end MTPAux6L

namespace MTPAux3
open RobustPrefLearn.MTP

/-- `λ^OA_*` transported to the prefix sets of a ranking `σ`. -/
noncomputable def lamR {K : ℕ} (p : ℝ) (σ : Equiv.Perm (Fin K)) : DS K → ℝ := by
  classical
  exact fun S => ∑ n ∈ Finset.Icc 2 K,
    (if S.1 = topSet σ n then lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m else 0)

lemma lamR_simplex {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (σ : Equiv.Perm (Fin K)) : lamR p σ ∈ simplex K := by
  classical
  set Λ := ∑ m ∈ Finset.Icc 2 K, lamStar K p m
  have hΛ : 0 < Λ := MTPAux.lamStar_sum_pos K hK p hp0 hp1
  have hc : ∀ n ∈ Finset.Icc 2 K, 0 ≤ lamStar K p n / Λ := fun n hn =>
    div_nonneg (MTPAux.lamStar_nonneg K p hp0 hp1 n (Finset.mem_Icc.1 hn).1) hΛ.le
  have hcard : ∀ n ∈ Finset.Icc 2 K, 2 ≤ (topSet σ n).card := by
    intro n hn
    rw [MTPAux.card_topSet σ n (Finset.mem_Icc.1 hn).2]; exact (Finset.mem_Icc.1 hn).1
  refine ⟨fun S => Finset.sum_nonneg fun n hn => by split_ifs; exacts [hc n hn, le_rfl], ?_⟩
  unfold lamR
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun n hn => MTPAux6L.inner_eval' (topSet σ n) (hcard n hn)
    (fun _ => lamStar K p n / Λ))]
  rw [← Finset.sum_div, div_self hΛ.ne']

/-- `∑_S λ^σ(S) E_f[ξ^{σ'} | S] ≥ u*` for every `σ'` with a top different from that of `σ_f`. -/
theorem lamR_ES {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K)))
    (σf : Equiv.Perm (Fin K)) (hRf : Ranks f σf) (hPf : PSep p f σf)
    (σ' : Equiv.Perm (Fin K)) (hd : diffTop σf σ') :
    uStar K p ≤ ∑ S, lamR p σf S * MTPAux6L.ES p f σf σ' S := by
  classical
  set Λ := ∑ m ∈ Finset.Icc 2 K, lamStar K p m with hΛ
  have hΛpos : 0 < Λ := MTPAux.lamStar_sum_pos K hK p hp0 hp1
  have hc : ∀ n ∈ Finset.Icc 2 K, 0 ≤ lamStar K p n / Λ := fun n hn =>
    div_nonneg (MTPAux.lamStar_nonneg K p hp0 hp1 n (Finset.mem_Icc.1 hn).1) hΛpos.le
  unfold lamR
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hcard : ∀ n ∈ Finset.Icc 2 K, 2 ≤ (topSet σf n).card := by
    intro n hn
    rw [MTPAux.card_topSet σf n (Finset.mem_Icc.1 hn).2]; exact (Finset.mem_Icc.1 hn).1
  set k := σ'.symm ⟨0, by omega⟩ with hk
  have hk0 : (σ' k).val = 0 := by simp [hk]
  have hfk : (σf k).val ≠ 0 := fun e => hd k e hk0
  set M := (σf k).val + 1 with hM
  have hM2 : 2 ≤ M := by omega
  have hMK : M ≤ K := by have := (σf k).2; omega
  have hterm : ∀ n ∈ Finset.Icc 2 K,
      (if M ≤ n then aSeq p M / Λ * (lamStar K p n / bSeq p n) else 0) ≤
      ∑ S : DS K, (if S.1 = topSet σf n then lamStar K p n / Λ else 0) *
        MTPAux6L.ES p f σf σ' S := by
    intro n hn
    have e : ∀ S : DS K, (if S.1 = topSet σf n then lamStar K p n / Λ else 0) *
        MTPAux6L.ES p f σf σ' S =
        if S.1 = topSet σf n then lamStar K p n / Λ * MTPAux6L.ES p f σf σ' S else 0 := by
      intro S; split_ifs <;> simp
    simp_rw [e]
    rw [MTPAux6L.inner_eval' (topSet σf n) (hcard n hn)
      (fun S => lamStar K p n / Λ * MTPAux6L.ES p f σf σ' S)]
    by_cases hMn : M ≤ n
    · rw [if_pos hMn]
      have hkT : k ∈ topSet σf n := by simp [topSet]; omega
      have hdc := MTPAux6L.drift_claim p hp0 hp1 f hf σf hRf hPf σ' k hk0
        ⟨topSet σf n, hcard n hn⟩ hkT
      have hrel : relRank σf ⟨topSet σf n, hcard n hn⟩ k = M := by
        rw [hM, ← MTPAux6f.relRank_univ hK σf k]
        unfold relRank
        congr 1
        ext Y
        simp only [topSet, MTPAux6f.Uset, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.le_def]
        omega
      rw [hrel, MTPAux.card_topSet σf n (Finset.mem_Icc.1 hn).2] at hdc
      calc aSeq p M / Λ * (lamStar K p n / bSeq p n) =
            lamStar K p n / Λ * (aSeq p M / bSeq p n) := by ring
        _ ≤ lamStar K p n / Λ * MTPAux6L.ES p f σf σ' ⟨topSet σf n, hcard n hn⟩ :=
            mul_le_mul_of_nonneg_left hdc (hc n hn)
    · rw [if_neg hMn]
      exact mul_nonneg (hc n hn) (MTPAux6L.ES_nonneg p hp0 hp1 f hf σf hPf σ' _)
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [← Finset.sum_filter]
  have hfilt : (Finset.Icc 2 K).filter (fun n => M ≤ n) = Finset.Icc (K - (K - M)) K := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hfilt, ← Finset.mul_sum, MTPAux7.telescope K p hp0 hp1 (K - M) (by omega)]
  have e : K - (K - M) = M := by omega
  rw [e]
  have ha := MTPAux7.aSeq_pos p hp0 hp1 M hM2
  unfold uStar
  rw [← hΛ]
  apply le_of_eq
  field_simp

/-- `D_S(f‖g) ≥ E_f[log f^OA_{σ_f}/f^OA_{σ_g}]` for `p`-separable `g` with ranking `σ_g`. -/
lemma DS_ge_ES {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f g : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (hg : g ∈ (Mp p : Set (Pref K)))
    (σf σg : Equiv.Perm (Fin K)) (hPg : PSep p g σg) (S : DS K) :
    MTPAux6L.ES p f σf σg S ≤ DS_ f g S := by
  rw [MTPAux6L.ES_eq p f hf]
  unfold DS_
  have hr := MTPAux10.ratio_sum_le_one p hp0 hp1 g hg σg hPg σf S
  have h1 : ∑ X ∈ S.1, (f S X * Real.log (oa p σf S X / oa p σg S X) + f S X -
      oa p σf S X / oa p σg S X * g S X) ≤ ∑ X ∈ S.1, f S X * Real.log (f S X / g S X) :=
    Finset.sum_le_sum fun X hX => MTPAux1i.plog _ _ _ _ (MTPAux1i.f_nonneg hf S X)
      (MTPAux1i.f_nonneg hg S X)
      (div_pos (MTPAux6L.oa_pos p hp0 hp1 σf S X hX) (MTPAux6L.oa_pos p hp0 hp1 σg S X hX))
      (fun _ => ⟨(hg.1 S X).1 hX, rfl⟩)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hf.2.1 S] at h1
  have h2 : ∑ X ∈ S.1, oa p σf S X / oa p σg S X * g S X ≤ 1 := by
    calc _ = ∑ X ∈ S.1, g S X * (oa p σf S X / oa p σg S X) :=
          Finset.sum_congr rfl fun X _ => by ring
      _ ≤ 1 := hr
  have h3 : ∑ X ∈ S.1, f S X * MTPAux6L.xi p σf σg (S, X) =
      ∑ X ∈ S.1, f S X * Real.log (oa p σf S X / oa p σg S X) := by
    refine Finset.sum_congr rfl fun X hX => ?_
    unfold MTPAux6L.xi
    rw [Real.log_div (MTPAux6L.oa_pos p hp0 hp1 σf S X hX).ne'
      (MTPAux6L.oa_pos p hp0 hp1 σg S X hX).ne']
  rw [h3]
  linarith

/-- Lower bound: `I_*(f) ≥ u*` for every `f ∈ M_p`. -/
theorem Istar_ge {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) :
    ENNReal.ofReal (uStar K p) ≤ ⨅ g ∈ alt p f,
      ENNReal.ofReal (Dlam (lamR p (Classical.choose hf.2.2)) f g) := by
  obtain ⟨hRf, hPf⟩ := Classical.choose_spec hf.2.2
  set σf := Classical.choose hf.2.2
  have hlam := lamR_simplex hK p hp0 hp1 σf
  refine le_iInf₂ fun g hg => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨σg, hRg, hPg⟩ := hg.1.2.2
  have hd : diffTop σf σg := by
    intro k hk hk'
    exact hg.2 k k ⟨σf, hRf, hk⟩ ⟨σg, hRg, hk'⟩ rfl
  calc uStar K p ≤ ∑ S, lamR p σf S * MTPAux6L.ES p f σf σg S :=
        lamR_ES hK p hp0 hp1 f hf σf hRf hPf σg hd
    _ ≤ ∑ S, lamR p σf S * DS_ f g S :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left
          (DS_ge_ES p hp0 hp1 f g hf hg.1 σf σg hPg S) (hlam.1 S)
    _ = Dlam (lamR p σf) f g := rfl

theorem Istar_ge' {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) : ENNReal.ofReal (uStar K p) ≤ Istar p f := by
  refine (Istar_ge hK p hp0 hp1 f hf).trans ?_
  unfold Istar
  exact le_iSup₂ (f := fun lam (_ : lam ∈ simplex K) => ⨅ g ∈ alt p f,
    ENNReal.ofReal (Dlam lam f g)) _ (lamR_simplex hK p hp0 hp1 _)

end MTPAux3

namespace MTPAux3
open RobustPrefLearn.MTP

lemma oa_trans {K : ℕ} (p : ℝ) (σ τ : Equiv.Perm (Fin K)) (S : DS K) (X : Fin K) :
    oa p (σ.trans τ) S X = oa p τ (MTPAux6L.mapDS σ S) (σ X) := by
  unfold oa
  have hc : (MTPAux6L.mapDS σ S).1.card = S.1.card := by simp [MTPAux6L.mapDS]
  rw [hc, MTPAux6L.relRank_trans]
  by_cases hX : X ∈ S.1
  · rw [if_pos hX, if_pos ((MTPAux6L.mem_mapDS σ S X).2 hX)]
  · rw [if_neg hX, if_neg (fun h => hX ((MTPAux6L.mem_mapDS σ S X).1 h))]

lemma DS_trans {K : ℕ} (p : ℝ) (σ τ : Equiv.Perm (Fin K)) (S : DS K) :
    DS_ (oa p σ) (oa p (σ.trans τ)) S = DS_ (oa p 1) (oa p τ) (MTPAux6L.mapDS σ S) := by
  have h1 : oa p σ = oa p (σ.trans (1 : Equiv.Perm (Fin K))) := by
    congr 1
  unfold DS_
  conv_lhs => rw [h1]
  simp only [oa_trans]
  simp only [MTPAux6L.mapDS]
  rw [Finset.sum_map]
  rfl

/-- Weak duality: for every `λ`, the OA alternatives of `f^OA_σ` give `min ≤ l*`. -/
theorem inf_altOA_le {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (σ : Equiv.Perm (Fin K)) (lam : DS K → ℝ) (hlam : lam ∈ simplex K) :
    (⨅ g ∈ altOA p (oa p σ), ENNReal.ofReal (Dlam lam (oa p σ) g)) ≤
      ENNReal.ofReal (lStar K p) := by
  classical
  obtain ⟨hmu0, hmu1, hmuS⟩ := lemma_8 K hK p hp0 hp1
  set F := (Finset.univ : Finset (Equiv.Perm (Fin K))).filter (fun τ => NotTopOne τ)
  have hoaσ := MTPAux7.oa_mem p hp0 hp1 σ
  set I := ⨅ g ∈ altOA p (oa p σ), ENNReal.ofReal (Dlam lam (oa p σ) g)
  have halt : ∀ τ ∈ F, oa p (σ.trans τ) ∈ altOA p (oa p σ) := by
    intro τ hτ
    have hm := MTPAux7.oa_mem p hp0 hp1 (σ.trans τ)
    refine ⟨⟨σ.trans τ, rfl⟩, fun k k' hk hk' e => ?_⟩
    subst e
    have h1 := MTPAux1i.isTop_of_rank _ σ hoaσ.2 k hk
    have h2 := MTPAux1i.isTop_of_rank _ (σ.trans τ) hm.2 k hk'
    simp only [Equiv.trans_apply] at h2
    exact (Finset.mem_filter.1 hτ).2 (σ k) h2 h1
  have hI : ∀ τ ∈ F, I ≤ ENNReal.ofReal (Dlam lam (oa p σ) (oa p (σ.trans τ))) := fun τ hτ =>
    iInf₂_le (oa p (σ.trans τ)) (halt τ hτ)
  have hD0 : ∀ τ, 0 ≤ Dlam lam (oa p σ) (oa p (σ.trans τ)) := by
    intro τ
    exact Finset.sum_nonneg fun S _ => mul_nonneg (hlam.1 S)
      (MTPAux1i.DS_nonneg hoaσ.1 (MTPAux7.oa_mem p hp0 hp1 _).1 S)
  calc I = (∑ τ ∈ F, ENNReal.ofReal (muStar K p τ)) * I := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun τ _ => hmu0 τ), hmu1, ENNReal.ofReal_one, one_mul]
    _ = ∑ τ ∈ F, ENNReal.ofReal (muStar K p τ) * I := Finset.sum_mul _ _ _
    _ ≤ ∑ τ ∈ F, ENNReal.ofReal (muStar K p τ) *
          ENNReal.ofReal (Dlam lam (oa p σ) (oa p (σ.trans τ))) := by
        gcongr with τ hτ; exact hI τ hτ
    _ = ENNReal.ofReal (∑ τ ∈ F, muStar K p τ * Dlam lam (oa p σ) (oa p (σ.trans τ))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun τ _ => mul_nonneg (hmu0 τ) (hD0 τ))]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [ENNReal.ofReal_mul (hmu0 τ)]
    _ ≤ ENNReal.ofReal (lStar K p) := by
        apply ENNReal.ofReal_le_ofReal
        have e : ∑ τ ∈ F, muStar K p τ * Dlam lam (oa p σ) (oa p (σ.trans τ)) =
            ∑ S, lam S * ∑ τ ∈ F, DS_ (oa p 1) (oa p τ) (MTPAux6L.mapDS σ S) * muStar K p τ := by
          unfold Dlam
          simp_rw [Finset.mul_sum, DS_trans]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun τ _ => ?_
          ring
        rw [e]
        calc ∑ S, lam S * ∑ τ ∈ F, DS_ (oa p 1) (oa p τ) (MTPAux6L.mapDS σ S) * muStar K p τ
            ≤ ∑ S, lam S * lStar K p :=
              Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hmuS _) (hlam.1 S)
          _ = lStar K p := by rw [← Finset.sum_mul, hlam.2, one_mul]

lemma altOA_sub {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K) :
    altOA p f ⊆ alt p f := by
  rintro g ⟨⟨σ, rfl⟩, h⟩
  exact ⟨(MTPAux7.oa_mem p hp0 hp1 σ).1, h⟩

theorem Istar_oa_le {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (σ : Equiv.Perm (Fin K)) : Istar p (oa p σ) ≤ ENNReal.ofReal (uStar K p) := by
  rw [lemma_9 K hK p hp0 hp1]
  unfold Istar
  refine iSup₂_le fun lam hlam => ?_
  refine le_trans ?_ (inf_altOA_le hK p hp0 hp1 σ lam hlam)
  exact le_iInf₂ fun g hg => iInf₂_le g (altOA_sub p hp0 hp1 _ hg)

theorem Istar_oa_eq {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (σ : Equiv.Perm (Fin K)) : Istar p (oa p σ) = ENNReal.ofReal (uStar K p) :=
  le_antisymm (Istar_oa_le hK p hp0 hp1 σ)
    (Istar_ge' hK p hp0 hp1 _ (MTPAux7.oa_mem p hp0 hp1 σ).1)

end MTPAux3

namespace MTPAux3
open RobustPrefLearn.MTP

theorem Istar_ge_of {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Pref K)
    (hf : f ∈ (Mp p : Set (Pref K))) (σf : Equiv.Perm (Fin K)) (hRf : Ranks f σf)
    (hPf : PSep p f σf) :
    ENNReal.ofReal (uStar K p) ≤ ⨅ g ∈ alt p f, ENNReal.ofReal (Dlam (lamR p σf) f g) := by
  have hlam := lamR_simplex hK p hp0 hp1 σf
  refine le_iInf₂ fun g hg => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨σg, hRg, hPg⟩ := hg.1.2.2
  have hd : diffTop σf σg := by
    intro k hk hk'
    exact hg.2 k k ⟨σf, hRf, hk⟩ ⟨σg, hRg, hk'⟩ rfl
  calc uStar K p ≤ ∑ S, lamR p σf S * MTPAux6L.ES p f σf σg S :=
        lamR_ES hK p hp0 hp1 f hf σf hRf hPf σg hd
    _ ≤ ∑ S, lamR p σf S * DS_ f g S :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left
          (DS_ge_ES p hp0 hp1 f g hf hg.1 σf σg hPg S) (hlam.1 S)
    _ = Dlam (lamR p σf) f g := rfl

theorem IOA_eq {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IOA (K := K) p = ENNReal.ofReal (uStar K p) := by
  apply le_antisymm (MTPAux6L.IOA_le hK p hp0 hp1)
  unfold IOA
  exact le_iInf₂ fun f hf => Istar_ge' hK p hp0 hp1 f hf

end MTPAux3

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

namespace MTPAux4u
open RobustPrefLearn.MTP

noncomputable def Bf (p : ℝ) (i : ℕ) : ℝ :=
  if i = 1 then 0 else if i = 2 then bSeq p 2 else bSeq p i - bSeq p (i - 1)

lemma Bf_sum (p : ℝ) : ∀ N, 2 ≤ N → ∑ j ∈ Finset.range N, Bf p (j + 1) = bSeq p N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp [Bf, Finset.sum_range_succ]
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Bf]
    rw [if_neg (by omega), if_neg (by omega)]
    simp

lemma aSeq_strict (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 2 ≤ n) :
    aSeq p n < aSeq p (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold aSeq
  have hl := MTPAux8.log_pos' p hp0 hp1
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 + 1 - 1 = m + 2 := by omega
  rw [e1, e2]
  apply mul_lt_mul_of_pos_left _ hl
  have hpm : 0 < p ^ (m + 1) := pow_pos hp0 _
  have key : 1 - ((m + 2 + 1 : ℕ) : ℝ) * p ^ (m + 2) +
      (((m + 2 + 1 : ℕ) : ℝ) - 1) * p ^ (m + 2 + 1) =
      (1 - ((m + 2 : ℕ) : ℝ) * p ^ (m + 1) + (((m + 2 : ℕ) : ℝ) - 1) * p ^ (m + 2)) +
        ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
    push_cast; ring
  rw [key]
  have : 0 < ((m : ℝ) + 2) * p ^ (m + 1) * (1 - p) ^ 2 := by
    have : 0 < (1 - p) ^ 2 := by nlinarith
    positivity
  linarith

lemma aSeq_strict' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (i M : ℕ) (hi : 2 ≤ i) (hiM : i < M) :
    aSeq p i < aSeq p M := by
  induction M, hiM using Nat.le_induction with
  | base => exact aSeq_strict p hp0 hp1 i hi
  | succ M hM ih => exact ih.trans (aSeq_strict p hp0 hp1 M (by omega))

lemma muSeq_M (p : ℝ) (M : ℕ) (hM : 3 ≤ M) :
    muSeq p M = p ^ (M - 1) * (1 - p) / aSeq p M := by
  unfold muSeq bSeq
  rw [if_neg (by omega)]
  congr 1
  obtain ⟨k, hk⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  rw [hk]; simp [pow_succ]; ring

/-- `𝔞_i µ_M ≤ B(i)` for `2 ≤ i ≤ M`, strictly if `i < M`. -/
lemma core_le (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (i M : ℕ) (hi : 2 ≤ i) (hiM : i ≤ M) :
    aSeq p i * muSeq p M ≤ Bf p i ∧ (i < M → aSeq p i * muSeq p M < Bf p i) := by
  have hM2 : 2 ≤ M := by omega
  have haM := MTPAux8.aSeq_pos p hp0 hp1 M hM2
  have hai := MTPAux8.aSeq_pos p hp0 hp1 i hi
  have hp1' : 0 < 1 - p := by linarith
  by_cases hM : M = 2
  · subst hM
    have : i = 2 := by omega
    subst this
    refine ⟨?_, fun h => absurd h (lt_irrefl _)⟩
    simp only [Bf, muSeq, if_true]
    rw [if_neg (by norm_num), mul_div_cancel₀ _ haM.ne']
  have hmu := muSeq_M p M (by omega)
  rw [hmu]
  by_cases hi2 : i = 2
  · subst hi2
    simp only [Bf, if_true, show (2 : ℕ) ≠ 1 by norm_num, if_false]
    unfold bSeq
    have hlt : aSeq p 2 * (p ^ (M - 1) * (1 - p) / aSeq p M) < 1 - p ^ 2 := by
      rw [mul_div_assoc', div_lt_iff₀ haM]
      have hpM : p ^ (M - 1) < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
      have hmono := MTPAux8.aSeq_mono' p hp0 hp1 2 M le_rfl (by omega)
      have : aSeq p 2 * (p ^ (M - 1) * (1 - p)) ≤ aSeq p M * (p ^ (M - 1) * (1 - p)) := by
        apply mul_le_mul_of_nonneg_right hmono; positivity
      have : aSeq p M * (p ^ (M - 1) * (1 - p)) < aSeq p M * (1 - p ^ 2) := by
        apply mul_lt_mul_of_pos_left _ haM
        nlinarith
      linarith
    exact ⟨hlt.le, fun _ => hlt⟩
  · simp only [Bf]
    rw [if_neg (by omega), if_neg hi2]
    have hbi : bSeq p i - bSeq p (i - 1) = p ^ (i - 1) * (1 - p) := by
      unfold bSeq
      obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [hk]; simp [pow_succ]; ring
    rw [hbi, mul_div_assoc']
    have hmono := MTPAux8.aSeq_mono' p hp0 hp1 i M hi hiM
    have hpp : p ^ (M - 1) ≤ p ^ (i - 1) := pow_le_pow_of_le_one hp0.le hp1.le (by omega)
    refine ⟨?_, fun hlt => ?_⟩
    · rw [div_le_iff₀ haM]
      calc aSeq p i * (p ^ (M - 1) * (1 - p)) ≤ aSeq p M * (p ^ (i - 1) * (1 - p)) := by
            gcongr
        _ = _ := by ring
    · rw [div_lt_iff₀ haM]
      have hpp' : p ^ (M - 1) < p ^ (i - 1) :=
        pow_lt_pow_right_of_lt_one₀ hp0 hp1 (by omega)
      calc aSeq p i * (p ^ (M - 1) * (1 - p)) < aSeq p i * (p ^ (i - 1) * (1 - p)) := by
            apply mul_lt_mul_of_pos_left _ hai
            exact mul_lt_mul_of_pos_right hpp' hp1'
        _ ≤ aSeq p M * (p ^ (i - 1) * (1 - p)) := by
            apply mul_le_mul_of_nonneg_right hmono; positivity
        _ = _ := by ring

end MTPAux4u

namespace MTPAux4u
open RobustPrefLearn.MTP

lemma r_le {K : ℕ} (S : DS K) (m : Fin K) :
    (S.1.filter (fun k => k ≤ m)).card ≤ m.val + 1 := by
  calc (S.1.filter (fun k => k ≤ m)).card ≤ (Finset.univ.filter (fun k : Fin K => k ≤ m)).card := by
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

lemma r_zero {K : ℕ} (S : DS K) (m : Fin K) (hm : m.val = 0) (hmS : m ∈ S.1) :
    (S.1.filter (fun k => k ≤ m)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨m, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hk⟩; exact Fin.ext (by rw [Fin.le_def] at hk; omega)
  · rintro rfl; exact ⟨hmS, le_rfl⟩

/-- The value of the dual constraint at `S`. -/
noncomputable def V {K : ℕ} (p : ℝ) (S : DS K) : ℝ := by
  classical
  exact ∑ σbar ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin K) => NotTopOne σ),
    DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p σbar) S * muStar K p σbar

/-- Termwise bound in the dual constraint, strict at an element of rank `i ≥ 2` placed
after position `i`. -/
lemma term_bound {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (S : DS K)
    (m : Fin K) (Z : ℝ) (hZ : 0 < Z) :
    (if 1 ≤ m.val then
        DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat m)) S * (muSeq p (m.val + 1) / Z)
        else 0) ≤
      (if m ∈ S.1 then Bf p (S.1.filter (fun k => k ≤ m)).card else 0) / bSeq p S.1.card / Z ∧
    (1 ≤ m.val → m ∈ S.1 → 2 ≤ (S.1.filter (fun k => k ≤ m)).card →
      (S.1.filter (fun k => k ≤ m)).card < m.val + 1 →
      (if 1 ≤ m.val then
        DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat m)) S * (muSeq p (m.val + 1) / Z)
        else 0) <
      (if m ∈ S.1 then Bf p (S.1.filter (fun k => k ≤ m)).card else 0) / bSeq p S.1.card / Z) := by
  classical
  set n := S.1.card
  have hbn : 0 < bSeq p n := by
    unfold bSeq; have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by have := S.2; omega); linarith
  set r := (S.1.filter (fun k => k ≤ m)).card with hr
  have hrel : relRank (1 : Equiv.Perm (Fin K)) S m = r := by unfold relRank; rfl
  by_cases hm : 1 ≤ m.val
  · rw [if_pos hm, lemma_6 K hK p hp0 hp1 m hm S, hrel]
    by_cases hmS : m ∈ S.1
    · rw [if_pos hmS, if_pos hmS]
      have e : aSeq p r / bSeq p n * (muSeq p (m.val + 1) / Z) =
          aSeq p r * muSeq p (m.val + 1) / bSeq p n / Z := by ring
      rw [e]
      have hr1 : 1 ≤ r := Finset.card_pos.2 ⟨m, Finset.mem_filter.2 ⟨hmS, le_rfl⟩⟩
      have hrM : r ≤ m.val + 1 := r_le S m
      rcases Nat.lt_or_ge r 2 with h1 | h2
      · have : r = 1 := by omega
        rw [this, MTPAux8.aSeq_one]
        refine ⟨by simp [Bf], fun _ _ h => by omega⟩
      · obtain ⟨hle, hlt⟩ := core_le p hp0 hp1 r (m.val + 1) h2 hrM
        refine ⟨?_, fun _ _ _ hlt' => ?_⟩
        · exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hle hbn.le) hZ.le
        · exact div_lt_div_of_pos_right (div_lt_div_of_pos_right (hlt hlt') hbn) hZ
    · rw [if_neg hmS, if_neg hmS]
      exact ⟨by simp, fun _ h => absurd h hmS⟩
  · rw [if_neg hm]
    refine ⟨?_, fun h => absurd h hm⟩
    by_cases hmS : m ∈ S.1
    · rw [if_pos hmS]
      have : r = 1 := r_zero S m (by omega) hmS
      rw [this]; simp [Bf]
    · rw [if_neg hmS]; simp

lemma prefix_of_good {K : ℕ} (S : DS K)
    (hgood : ∀ m ∈ S.1, 2 ≤ (S.1.filter (fun k => k ≤ m)).card →
      (S.1.filter (fun k => k ≤ m)).card = m.val + 1) :
    ∃ n ∈ Finset.Icc 2 K, S.1 = prefixSet K n := by
  classical
  set n := S.1.card with hn
  have hn2 : 2 ≤ n := S.2
  have hnK : n ≤ K := by
    calc n ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_le_univ _
      _ = K := by simp
  have hrel : ∀ X, relRank (1 : Equiv.Perm (Fin K)) S X = (S.1.filter (fun k => k ≤ X)).card := by
    intro X; unfold relRank; rfl
  have hall : ∀ m ∈ S.1, (S.1.filter (fun k => k ≤ m)).card = m.val + 1 := by
    intro m hmS
    rcases Nat.lt_or_ge (S.1.filter (fun k => k ≤ m)).card 2 with h | h
    · -- `m` has rank 1; the element of rank 2 is version 2 (index 1)
      obtain ⟨Y, hY⟩ := (MTPAux10.rankEquiv (1 : Equiv.Perm (Fin K)) S).surjective
        ⟨1, by omega⟩
      have hYv := congrArg Fin.val hY
      rw [MTPAux10.rankEquiv_val, hrel] at hYv
      simp only at hYv
      have hY1 := MTPAux10.rank_ge_one 1 S Y.1 Y.2
      rw [hrel] at hY1
      have hY2 : (S.1.filter (fun k => k ≤ Y.1)).card = 2 := by omega
      have hYval := hgood Y.1 Y.2 (by omega)
      rw [hY2] at hYval
      have hm1 := MTPAux10.rank_ge_one 1 S m hmS
      rw [hrel] at hm1
      have hlt : relRank (1 : Equiv.Perm (Fin K)) S m < relRank 1 S Y.1 := by
        rw [hrel, hrel]; omega
      rw [MTPAux10.rank_lt_iff 1 S m Y.1 hmS Y.2] at hlt
      simp only [Equiv.Perm.one_apply, Fin.lt_def] at hlt
      omega
    · exact hgood m hmS h
  refine ⟨n, Finset.mem_Icc.2 ⟨hn2, hnK⟩, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro X hX
    have := hall X hX
    have h2 : (S.1.filter (fun k => k ≤ X)).card ≤ n := Finset.card_le_card (Finset.filter_subset _ _)
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · rw [MTPAux7.card_prefix K n hnK]

/-- The dual constraint is strict at every display set that is not a prefix set. -/
theorem V_lt {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (S : DS K)
    (hS : ¬ ∃ n ∈ Finset.Icc 2 K, S.1 = prefixSet K n) : V p S < lStar K p := by
  classical
  set Z := ∑ j ∈ Finset.Icc 2 K, muSeq p j with hZ
  have hZpos : 0 < Z := by
    calc 0 < muSeq p K := MTPAux8.muSeq_pos p hp0 hp1 K hK
      _ ≤ Z := Finset.single_le_sum (f := fun j => muSeq p j)
          (fun j hj => (MTPAux8.muSeq_pos p hp0 hp1 j (Finset.mem_Icc.1 hj).1).le)
          (Finset.mem_Icc.2 ⟨hK, le_rfl⟩)
  -- a bad element
  have hbad : ∃ m ∈ S.1, 2 ≤ (S.1.filter (fun k => k ≤ m)).card ∧
      (S.1.filter (fun k => k ≤ m)).card < m.val + 1 := by
    by_contra hc
    push_neg at hc
    exact hS (prefix_of_good S fun m hm h2 => le_antisymm (r_le S m) (hc m hm h2))
  obtain ⟨m0, hm0S, hm02, hm0lt⟩ := hbad
  have hm01 : 1 ≤ m0.val := by
    by_contra h
    have := r_zero S m0 (by omega) hm0S
    omega
  set n := S.1.card
  have hn2 : 2 ≤ n := S.2
  have hbn : 0 < bSeq p n := by
    unfold bSeq; have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega); linarith
  unfold V
  rw [MTPAux8.sum_muStar]
  calc _ < ∑ m : Fin K, (if m ∈ S.1 then Bf p (S.1.filter (fun k => k ≤ m)).card else 0) /
        bSeq p n / Z :=
        Finset.sum_lt_sum (fun m _ => (term_bound hK p hp0 hp1 S m Z hZpos).1)
          ⟨m0, Finset.mem_univ _, (term_bound hK p hp0 hp1 S m0 Z hZpos).2 hm01 hm0S hm02 hm0lt⟩
    _ = (∑ m ∈ S.1, Bf p (S.1.filter (fun k => k ≤ m)).card) / bSeq p n / Z := by
        rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_ite_mem, Finset.univ_inter]
    _ = lStar K p := by
        rw [MTPAux8.sum_rank (Bf p) S.1, Bf_sum p n hn2, div_self hbn.ne']
        unfold lStar; rw [← hZ]

theorem V_le {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (S : DS K) :
    V p S ≤ lStar K p := (lemma_8 K hK p hp0 hp1).2.2 S

end MTPAux4u

namespace MTPAux4u
open RobustPrefLearn.MTP

lemma topSet_one {K : ℕ} (n : ℕ) : topSet (1 : Equiv.Perm (Fin K)) n = prefixSet K n := by
  ext X
  unfold topSet prefixSet
  rw [Finset.mem_filter, Finset.mem_filter]
  simp

lemma lamR_one {K : ℕ} (p : ℝ) : MTPAux3.lamR p (1 : Equiv.Perm (Fin K)) = lamOA K p := by
  classical
  funext S
  unfold MTPAux3.lamR
  rw [MTPAux7.lamOA_eq]
  simp_rw [topSet_one]

lemma alt_oa {K : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (σ : Equiv.Perm (Fin K))
    (hσ : NotTopOne σ) : oa p σ ∈ alt p (oa p (1 : Equiv.Perm (Fin K))) := by
  have hoa1 := MTPAux7.oa_mem p hp0 hp1 (1 : Equiv.Perm (Fin K))
  have hσm := MTPAux7.oa_mem p hp0 hp1 σ
  refine ⟨hσm.1, fun k k' hk hk' e => ?_⟩
  subst e
  have h1 := MTPAux1i.isTop_of_rank _ 1 hoa1.2 k hk
  have h2 := MTPAux1i.isTop_of_rank _ σ hσm.2 k hk'
  exact hσ k h2 (by simpa using h1)

/-- `G(λ^OA_*) = u*`. -/
lemma G_lamOA {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
      ENNReal.ofReal (Dlam (lamOA K p) (oa p (1 : Equiv.Perm (Fin K))) g)) =
      ENNReal.ofReal (uStar K p) := by
  have hm := MTPAux7.oa_mem p hp0 hp1 (1 : Equiv.Perm (Fin K))
  apply le_antisymm
  · have h := MTPAux3.inf_altOA_le hK p hp0 hp1 1 (lamOA K p)
        (by rw [← lamR_one]; exact MTPAux3.lamR_simplex hK p hp0 hp1 1)
    rw [← lemma_9 K hK p hp0 hp1] at h
    refine le_trans ?_ h
    exact le_iInf₂ fun g hg => iInf₂_le g (MTPAux3.altOA_sub p hp0 hp1 _ hg)
  · rw [← lamR_one]
    exact MTPAux3.Istar_ge_of hK p hp0 hp1 _ hm.1 1 hm.2 (MTPAux5.psep_of_rank p _ 1 hm)

lemma G_le {K : ℕ} (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (lam : DS K → ℝ)
    (hlam : lam ∈ simplex K) :
    (⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
      ENNReal.ofReal (Dlam lam (oa p (1 : Equiv.Perm (Fin K))) g)) ≤
      ENNReal.ofReal (uStar K p) := by
  have h := MTPAux3.inf_altOA_le hK p hp0 hp1 1 lam hlam
  rw [← lemma_9 K hK p hp0 hp1] at h
  refine le_trans ?_ h
  exact le_iInf₂ fun g hg => iInf₂_le g (MTPAux3.altOA_sub p hp0 hp1 _ hg)

end MTPAux4u

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ n ∈ Finset.Icc 2 K, 0 < aSeq p n ∧ 0 < bSeq p n ∧ 0 < lamStar K p n) ∧
    lamOA K p ∈ simplex K ∧
    (∀ lam ∈ simplex K,
      (⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
          ENNReal.ofReal (Dlam lam (oa p (1 : Equiv.Perm (Fin K))) g)) ≤
        ⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
          ENNReal.ofReal (Dlam (lamOA K p) (oa p (1 : Equiv.Perm (Fin K))) g)) ∧
    (∀ lam ∈ simplex K,
      (⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
          ENNReal.ofReal (Dlam lam (oa p (1 : Equiv.Perm (Fin K))) g)) =
        (⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
          ENNReal.ofReal (Dlam (lamOA K p) (oa p (1 : Equiv.Perm (Fin K))) g)) →
      lam = lamOA K p) := by
  classical
  have hb : ∀ n, 1 ≤ n → 0 < bSeq p n := by
    intro n hn
    unfold bSeq; have : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 (by omega); linarith
  refine ⟨fun n hn => ?_, ?_, fun lam hlam => ?_, fun lam hlam heq => ?_⟩
  · obtain ⟨hn2, hnK⟩ := Finset.mem_Icc.1 hn
    have ha := MTPAux8.aSeq_pos p hp0 hp1 n hn2
    refine ⟨ha, hb n (by omega), ?_⟩
    unfold lamStar
    split_ifs with h
    · apply mul_pos (hb n (by omega))
      rw [sub_pos]
      exact one_div_lt_one_div_of_lt ha (MTPAux4u.aSeq_strict p hp0 hp1 n hn2)
    · exact div_pos (hb n (by omega)) ha
  · rw [← MTPAux4u.lamR_one]; exact MTPAux3.lamR_simplex hK p hp0 hp1 1
  · rw [MTPAux4u.G_lamOA hK p hp0 hp1]; exact MTPAux4u.G_le hK p hp0 hp1 lam hlam
  -- uniqueness
  rw [MTPAux4u.G_lamOA hK p hp0 hp1] at heq
  obtain ⟨hmu0, hmu1, hmuS⟩ := lemma_8 K hK p hp0 hp1
  have h9 := lemma_9 K hK p hp0 hp1
  set u := uStar K p with hu_def
  have hu := MTPAux6L.uStar_pos hK p hp0 hp1
  set F := (Finset.univ : Finset (Equiv.Perm (Fin K))).filter (fun σ => NotTopOne σ)
  set D : Equiv.Perm (Fin K) → ℝ := fun σ => Dlam lam (oa p (1 : Equiv.Perm (Fin K))) (oa p σ)
  have hoa1 := MTPAux7.oa_mem p hp0 hp1 (1 : Equiv.Perm (Fin K))
  have hD0 : ∀ σ, 0 ≤ D σ := fun σ => Finset.sum_nonneg fun S _ => mul_nonneg (hlam.1 S)
    (MTPAux1i.DS_nonneg hoa1.1 (MTPAux7.oa_mem p hp0 hp1 σ).1 S)
  have hDu : ∀ σ ∈ F, u ≤ D σ := by
    intro σ hσ
    have h1 : ENNReal.ofReal u ≤ ENNReal.ofReal (D σ) := by
      rw [← heq]
      exact iInf₂_le (oa p σ) (MTPAux4u.alt_oa p hp0 hp1 σ (Finset.mem_filter.1 hσ).2)
    exact (ENNReal.ofReal_le_ofReal_iff (hD0 σ)).1 h1
  have hswap : ∑ σ ∈ F, muStar K p σ * D σ = ∑ S, lam S * MTPAux4u.V p S := by
    unfold MTPAux4u.V
    simp only [D, Dlam]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  have hVsum : ∑ S, lam S * MTPAux4u.V p S ≤ u := by
    rw [h9]
    calc ∑ S, lam S * MTPAux4u.V p S ≤ ∑ S, lam S * lStar K p :=
          Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left
            (MTPAux4u.V_le hK p hp0 hp1 S) (hlam.1 S)
      _ = lStar K p := by rw [← Finset.sum_mul, hlam.2, one_mul]
  have hDsum : u ≤ ∑ σ ∈ F, muStar K p σ * D σ := by
    calc u = ∑ σ ∈ F, muStar K p σ * u := by rw [← Finset.sum_mul, hmu1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun σ hσ => mul_le_mul_of_nonneg_left (hDu σ hσ) (hmu0 σ)
  -- complementary slackness (primal)
  have hslack : ∀ S, lam S * (lStar K p - MTPAux4u.V p S) = 0 := by
    have hnn : ∀ S ∈ (Finset.univ : Finset (DS K)), 0 ≤ lam S * (lStar K p - MTPAux4u.V p S) :=
      fun S _ => mul_nonneg (hlam.1 S) (by linarith [MTPAux4u.V_le hK p hp0 hp1 S])
    have hs : ∑ S, lam S * (lStar K p - MTPAux4u.V p S) = 0 := by
      apply le_antisymm _ (Finset.sum_nonneg hnn)
      have : ∑ S, lam S * (lStar K p - MTPAux4u.V p S) =
          lStar K p - ∑ S, lam S * MTPAux4u.V p S := by
        rw [Finset.sum_congr rfl (fun S _ => mul_sub (lam S) _ _), Finset.sum_sub_distrib,
          ← Finset.sum_mul, hlam.2, one_mul]
      rw [this, ← h9]; linarith
    intro S
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hs S (Finset.mem_univ S)
  have hsupp : ∀ S : DS K, (¬ ∃ n ∈ Finset.Icc 2 K, S.1 = prefixSet K n) → lam S = 0 := by
    intro S hS
    have h1 := hslack S
    have h2 := MTPAux4u.V_lt hK p hp0 hp1 S hS
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · linarith
  -- complementary slackness (dual): `D(σ̂_m) = u*`
  have hDm : ∀ m : Fin K, 1 ≤ m.val → D (sigmaHat m) = u := by
    intro m hm
    have hnn : ∀ σ ∈ F, 0 ≤ muStar K p σ * (D σ - u) :=
      fun σ hσ => mul_nonneg (hmu0 σ) (by linarith [hDu σ hσ])
    have hs : ∑ σ ∈ F, muStar K p σ * (D σ - u) = 0 := by
      apply le_antisymm _ (Finset.sum_nonneg hnn)
      have : ∑ σ ∈ F, muStar K p σ * (D σ - u) = ∑ σ ∈ F, muStar K p σ * D σ - u := by
        rw [Finset.sum_congr rfl (fun σ _ => mul_sub (muStar K p σ) _ _), Finset.sum_sub_distrib,
          ← Finset.sum_mul, hmu1, one_mul]
      rw [this, hswap]; linarith
    have hmem : sigmaHat m ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, MTPAux8.notTop_hat m hm⟩
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hs _ hmem
    have hZpos : 0 < ∑ j ∈ Finset.Icc 2 K, muSeq p j := by
      calc 0 < muSeq p K := MTPAux8.muSeq_pos p hp0 hp1 K hK
        _ ≤ _ := Finset.single_le_sum (f := fun j => muSeq p j)
            (fun j hj => (MTPAux8.muSeq_pos p hp0 hp1 j (Finset.mem_Icc.1 hj).1).le)
            (Finset.mem_Icc.2 ⟨hK, le_rfl⟩)
    have hmupos : 0 < muStar K p (sigmaHat m) := by
      unfold muStar
      calc 0 < muSeq p (m.val + 1) / ∑ j ∈ Finset.Icc 2 K, muSeq p j :=
            div_pos (MTPAux8.muSeq_pos p hp0 hp1 _ (by omega)) hZpos
        _ = (if 1 ≤ m.val ∧ sigmaHat m = sigmaHat m then
              muSeq p (m.val + 1) / ∑ j ∈ Finset.Icc 2 K, muSeq p j else 0) := by
            rw [if_pos ⟨hm, rfl⟩]
        _ ≤ _ := Finset.single_le_sum (f := fun m' : Fin K =>
              if 1 ≤ m'.val ∧ sigmaHat m = sigmaHat m' then
                muSeq p (m'.val + 1) / ∑ j ∈ Finset.Icc 2 K, muSeq p j else 0)
              (fun m' _ => by
                split_ifs
                · exact div_nonneg (MTPAux8.muSeq_pos p hp0 hp1 _ (by omega)).le hZpos.le
                · exact le_rfl) (Finset.mem_univ m)
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · linarith
  -- the weights on prefix sets
  have hcard : ∀ n ∈ Finset.Icc 2 K, 2 ≤ (prefixSet K n).card := by
    intro n hn
    rw [MTPAux7.card_prefix K n (Finset.mem_Icc.1 hn).2]; exact (Finset.mem_Icc.1 hn).1
  set w : ℕ → ℝ := fun n => if h : 2 ≤ (prefixSet K n).card then lam ⟨prefixSet K n, h⟩ else 0
    with hw
  have hlamS : ∀ S : DS K, lam S = ∑ n ∈ Finset.Icc 2 K,
      (if S.1 = prefixSet K n then lam S else 0) := by
    intro S
    by_cases hS : ∃ n ∈ Finset.Icc 2 K, S.1 = prefixSet K n
    · obtain ⟨n, hn, hSn⟩ := hS
      rw [Finset.sum_eq_single n]
      · rw [if_pos hSn]
      · intro b hb hbn
        rw [if_neg]
        intro hSb
        apply hbn
        have := congrArg Finset.card (hSn.symm.trans hSb)
        rwa [MTPAux7.card_prefix K n (Finset.mem_Icc.1 hn).2,
          MTPAux7.card_prefix K b (Finset.mem_Icc.1 hb).2, eq_comm] at this
      · intro h'; exact absurd hn h'
    · rw [hsupp S hS]; symm
      apply Finset.sum_eq_zero; intro n hn
      rw [if_neg (fun h => hS ⟨n, hn, h⟩)]
  have hDexp : ∀ m : Fin K, 1 ≤ m.val → D (sigmaHat m) =
      ∑ n ∈ Finset.Icc 2 K, w n * (if m.val + 1 ≤ n then aSeq p (m.val + 1) / bSeq p n else 0) := by
    intro m hm
    simp only [D, Dlam]
    rw [Finset.sum_congr rfl (fun S _ => by rw [hlamS S])]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    have e : ∀ S : DS K, (if S.1 = prefixSet K n then lam S else 0) *
        DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat m)) S =
        if S.1 = prefixSet K n then lam S *
          DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat m)) S else 0 := by
      intro S; split_ifs <;> simp
    simp_rw [e]
    rw [MTPAux6L.inner_eval' (prefixSet K n) (hcard n hn)
      (fun S => lam S * DS_ (oa p (1 : Equiv.Perm (Fin K))) (oa p (sigmaHat m)) S)]
    simp only [hw, dif_pos (hcard n hn)]
    congr 1
    rw [lemma_6 K hK p hp0 hp1 m hm]
    have hnK := (Finset.mem_Icc.1 hn).2
    by_cases hMn : m.val + 1 ≤ n
    · have hmem : m ∈ prefixSet K n := by simp [prefixSet]; omega
      rw [if_pos hmem, if_pos hMn]
      have hrr : relRank (1 : Equiv.Perm (Fin K)) ⟨prefixSet K n, hcard n hn⟩ m = m.val + 1 := by
        unfold relRank
        have : (prefixSet K n).filter (fun x => (1 : Equiv.Perm (Fin K)) x ≤
            (1 : Equiv.Perm (Fin K)) m) = Finset.univ.filter (fun x : Fin K => x.val < m.val + 1) := by
          ext x
          simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and,
            Equiv.Perm.one_apply, Fin.le_def]
          omega
        simp only at this ⊢
        rw [this, Fin.card_filter_val_lt]
        have := m.2
        omega
      rw [hrr]
      rw [show ((⟨prefixSet K n, hcard n hn⟩ : DS K).1.card) = n from
        MTPAux7.card_prefix K n hnK]
    · have hmem : m ∉ prefixSet K n := by simp [prefixSet]; omega
      rw [if_neg hmem, if_neg hMn]
  -- triangular system
  have hT : ∀ M, 2 ≤ M → M ≤ K → ∑ n ∈ Finset.Icc M K, w n / bSeq p n = u / aSeq p M := by
    intro M hM2 hMK
    have hm : 1 ≤ (⟨M - 1, by omega⟩ : Fin K).val := by simp; omega
    have h1 := hDm ⟨M - 1, by omega⟩ hm
    rw [hDexp _ hm] at h1
    simp only [show M - 1 + 1 = M by omega] at h1
    have ha := MTPAux8.aSeq_pos p hp0 hp1 M hM2
    have e : ∑ n ∈ Finset.Icc 2 K, w n * (if M ≤ n then aSeq p M / bSeq p n else 0) =
        aSeq p M * ∑ n ∈ Finset.Icc M K, w n / bSeq p n := by
      rw [Finset.mul_sum]
      rw [show Finset.Icc M K = (Finset.Icc 2 K).filter (fun n => M ≤ n) by
        ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    rw [e] at h1
    field_simp
    linarith
  have hwn : ∀ n ∈ Finset.Icc 2 K, w n = u * lamStar K p n := by
    intro n hn
    obtain ⟨hn2, hnK⟩ := Finset.mem_Icc.1 hn
    have hbn := hb n (by omega)
    unfold lamStar
    by_cases hnlt : n < K
    · rw [if_pos hnlt]
      have h1 := hT n hn2 hnK
      have h2 := hT (n + 1) (by omega) (by omega)
      have hins : Finset.Icc n K = insert n (Finset.Icc (n + 1) K) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hins, Finset.sum_insert (by simp), h2] at h1
      have : w n / bSeq p n = u / aSeq p n - u / aSeq p (n + 1) := by linarith
      rw [div_eq_iff hbn.ne'] at this
      rw [this]; ring
    · rw [if_neg hnlt]
      have hnK' : n = K := by omega
      have h1 := hT n hn2 hnK
      rw [show Finset.Icc n K = {n} by ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega,
        Finset.sum_singleton, div_eq_iff hbn.ne'] at h1
      rw [h1]; ring
  -- conclusion
  funext S
  by_cases hS : ∃ n ∈ Finset.Icc 2 K, S.1 = prefixSet K n
  · obtain ⟨n, hn, hSn⟩ := hS
    have hSeq : S = ⟨prefixSet K n, hcard n hn⟩ := Subtype.ext hSn
    have hlw : lam S = w n := by simp only [hw, dif_pos (hcard n hn)]; rw [hSeq]
    rw [hlw, hwn n hn]
    unfold lamOA
    rw [if_pos ⟨n, hn, hSn⟩, hSn, MTPAux7.card_prefix K n (Finset.mem_Icc.1 hn).2, hu_def]
    unfold uStar; ring
  · rw [hsupp S hS]
    unfold lamOA
    rw [if_neg hS]
