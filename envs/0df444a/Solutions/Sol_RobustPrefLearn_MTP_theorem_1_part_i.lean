-- Prove2me | solution 1 for RobustPrefLearn.MTP.theorem_1_part_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:40:44.49018+00:00
-- url     : https://prove2.me/submissions/d108080a-c75c-48a6-a5b3-86a97ce0b3ae

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Policy

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


open RobustPrefLearn.MTP in
theorem solution (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ π : Policy K, IsDeltaAccurate p δ π →
      ∀ f ∈ (Mp p : Set (Pref K)),
        ENNReal.ofReal (kl δ (1 - δ)) ≤ Istar p f * expTau π f := by
  intro δ hδ0 hδ π hacc f hf
  have hπ := hacc.1
  by_cases hE : expTau π f = ⊤
  · rw [hE, ENNReal.mul_top (MTPAux1i.Istar_pos hK p hp0 hp1 f hf)]; exact le_top
  by_cases hk : kl δ (1 - δ) ≤ 0
  · rw [ENNReal.ofReal_of_nonpos hk]; exact zero_le'
  rw [not_le] at hk
  set E := (expTau π f).toReal with hEdef
  have hEeq : ENNReal.ofReal E = expTau π f := ENNReal.ofReal_toReal hE
  have hN0 : ∀ S, 0 ≤ (MTPAux1i.Nexp π f S).toReal := fun _ => ENNReal.toReal_nonneg
  have hsumN : ∑ S, (MTPAux1i.Nexp π f S).toReal = E := by
    rw [← ENNReal.toReal_sum (fun S _ => MTPAux1i.Nexp_ne_top π hπ f hE S),
      MTPAux1i.sum_Nexp π hπ f]
  rcases (ENNReal.toReal_nonneg : (0 : ℝ) ≤ E).lt_or_eq with hEpos | hE0
  · set lam : DS K → ℝ := fun S => (MTPAux1i.Nexp π f S).toReal / E
    have hlam : lam ∈ simplex K := by
      refine ⟨fun S => div_nonneg (hN0 S) hEpos.le, ?_⟩
      simp only [lam]
      rw [← Finset.sum_div, hsumN, div_self hEpos.ne']
    have key : ∀ g ∈ alt p f, kl δ (1 - δ) / E ≤ Dlam lam f g := by
      intro g hg
      have := MTPAux1i.main_ineq p δ hδ0 hδ π hacc f hf g hg hE
      unfold Dlam
      simp only [lam]
      rw [div_le_iff₀ hEpos, Finset.sum_mul]
      refine this.trans (le_of_eq (Finset.sum_congr rfl fun S _ => ?_))
      have hE1 : E ≠ 0 := hEpos.ne'
      rw [← hEdef]
      field_simp
    have hI : ENNReal.ofReal (kl δ (1 - δ) / E) ≤ Istar p f := by
      unfold Istar
      refine le_trans ?_ (le_iSup₂ (f := fun lam (_ : lam ∈ simplex K) =>
        ⨅ g ∈ alt p f, ENNReal.ofReal (Dlam lam f g)) lam hlam)
      exact le_iInf₂ fun g hg => ENNReal.ofReal_le_ofReal (key g hg)
    calc ENNReal.ofReal (kl δ (1 - δ)) = ENNReal.ofReal (kl δ (1 - δ) / E) * ENNReal.ofReal E := by
          rw [← ENNReal.ofReal_mul (div_nonneg hk.le hEpos.le), div_mul_cancel₀ _ hEpos.ne']
      _ ≤ Istar p f * expTau π f := by rw [hEeq]; gcongr
  · exfalso
    obtain ⟨g, hg⟩ := MTPAux1i.alt_nonempty hK p hp0 hp1 f hf
    have h := MTPAux1i.main_ineq p δ hδ0 hδ π hacc f hf g hg hE
    have hz : ∀ S ∈ Finset.univ, (MTPAux1i.Nexp π f S).toReal = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun S _ => hN0 S)).1 (by rw [hsumN]; exact hE0.symm)
    rw [Finset.sum_eq_zero (fun S hS => by rw [hz S hS, mul_zero])] at h
    linarith
