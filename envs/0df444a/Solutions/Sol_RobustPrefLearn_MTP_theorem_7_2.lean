-- Prove2me | solution 2 for RobustPrefLearn.MTP.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:49:51.073665+00:00
-- url     : https://prove2.me/submissions/83769512-ab43-4bc5-bf4b-0749ad74dea1

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp
import Theorems.Thm_RobustPrefLearn_MTP_lemma_10
import Theorems.Thm_RobustPrefLearn_MTP_theorem_6_finite

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

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) [NeZero K] (hK : 2 ≤ K) :
    ∃ C1 : ℝ, ∀ p : ℝ, 0 < p → p < 1 → ∀ (S1 : DS K), ∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ β : ℝ,
      C1 + Real.log (1 / δ) ≤ β → IsDeltaAccurate p δ (mtp p S1 β) := by
  obtain ⟨C, hC⟩ := lemma_10 K hK
  refine ⟨Real.log (max C 1), fun p hp0 hp1 S1 δ hδ β hβ => ?_⟩
  have hlog : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [lt_one_div (by norm_num) hδ.1]
    simpa using hδ.2
  have hC1 : 0 ≤ Real.log (max C 1) := Real.log_nonneg (le_max_right _ _)
  have hβpos : 0 < β := by linarith
  refine ⟨MTPAux.mtp_admissible hK p hp0 hp1 S1 β, fun f hf => ⟨?_, ?_⟩⟩
  · -- `τ < ∞` almost surely, from `E_f[τ] < ∞` (Theorem 6 with the constant threshold `β`)
    have h6 := theorem_6_finite K hK p hp0 hp1 β S1 f hf
    exact MTPAux.probStop_eq_one p _ (MTPAux.mtp_admissible hK p hp0 hp1 S1 β) f hf h6
  · -- error probability `≤ C e^{-β} ≤ δ`
    refine (hC p hp0 hp1 S1 β hβpos f hf).trans (ENNReal.ofReal_le_ofReal ?_)
    have hmax : C ≤ Real.exp (Real.log (max C 1)) := by
      rw [Real.exp_log (by positivity)]; exact le_max_left _ _
    calc C * Real.exp (-β) ≤ Real.exp (Real.log (max C 1)) * Real.exp (-β) :=
          mul_le_mul_of_nonneg_right hmax (Real.exp_pos _).le
      _ = Real.exp (Real.log (max C 1) - β) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-Real.log (1 / δ)) := Real.exp_le_exp.2 (by linarith)
      _ = δ := by
          rw [Real.exp_neg, Real.exp_log (by have := hδ.1; positivity)]
          simp
