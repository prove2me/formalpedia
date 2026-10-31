-- Prove2me | solution 1 for RobustPrefLearn.MTP.theorem_6_finite
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T14:49:41.643716+00:00
-- url     : https://prove2.me/submissions/01dd4d31-4f26-40dd-b159-a1df93ab382a

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Mtp

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

namespace MTPAux1i
open RobustPrefLearn.MTP

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

open RobustPrefLearn.MTP in
theorem solution (K : ℕ) [NeZero K] (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (β : ℝ) (S1 : DS K) (f : Pref K) (hf : f ∈ (Mp p : Set (Pref K))) :
    expTau (mtp p S1 β) f < ⊤ := by
  classical
  set π := mtp p S1 β
  have hπ : Admissible π := MTPAux.mtp_admissible hK p hp0 hp1 S1 β
  set U := MTPAux6f.Uset K hK
  -- the smallest vote probability on `[K]`
  obtain ⟨Xmin, -, hXmin⟩ := Finset.exists_min_image Finset.univ (fun X => f U X)
    Finset.univ_nonempty
  set η := ENNReal.ofReal (f U Xmin)
  have hηpos : 0 < f U Xmin := (hf.1 U Xmin).1 (by simp [U, MTPAux6f.Uset])
  set q := ENNReal.ofReal (lamStar K p K / ∑ m ∈ Finset.Icc 2 K, lamStar K p m)
  have hqpos : 0 < lamStar K p K / ∑ m ∈ Finset.Icc 2 K, lamStar K p m := by
    apply div_pos _ (MTPAux.lamStar_sum_pos K hK p hp0 hp1)
    unfold lamStar
    rw [if_neg (lt_irrefl K)]
    have hb : 0 < bSeq p K := by
      unfold bSeq; have : p ^ K < 1 := pow_lt_one₀ hp0.le hp1 (by omega); linarith
    have := MTPAux.aSeq_pos p hp0 hp1 K hK
    positivity
  have hL : 0 < Real.log (1 / p) := by
    apply Real.log_pos; rw [lt_one_div (by norm_num) hp0]; simpa using hp1
  set m := ⌈β / Real.log (1 / p)⌉₊ + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hmβ : β ≤ m * Real.log (1 / p) := by
    have h1 : β / Real.log (1 / p) ≤ ⌈β / Real.log (1 / p)⌉₊ := Nat.le_ceil _
    have h2 : (⌈β / Real.log (1 / p)⌉₊ : ℝ) ≤ m := by simp [hm]
    rw [div_le_iff₀ hL] at h1
    nlinarith
  set ε := (q * η) ^ m
  have hεt : ε ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top)
  have hε0 : ε ≠ 0 := by
    apply pow_ne_zero
    apply mul_ne_zero
    · simpa [q] using hqpos
    · simpa [η] using hηpos
  have hgood : ∀ h : List (Step K), h ≠ [] → survives π h → ∃ b : Fin m → Step K,
      ¬ survives π (toHist b ++ h) ∧ ε * pathProb π f h ≤ pathProb π f (toHist b ++ h) := by
    intro h hh _
    set σh := (MTPAux.mle_nonempty p h).choose
    have hσh : σh ∈ mle p h := (MTPAux.mle_nonempty p h).choose_spec
    refine ⟨fun _ => (U, σh.symm 0), ?_, ?_⟩
    · rw [MTPAux6f.toHist_const]
      intro hs
      exact hs 0 (Nat.zero_le _) (by
        simpa using MTPAux6f.stop_good hK p hp0 hp1 S1 β h σh hσh m hm1 hmβ)
    · rw [MTPAux6f.toHist_const]
      exact MTPAux6f.path_good hK p S1 β f (σh.symm 0) h hh q η rfl
        (ENNReal.ofReal_le_ofReal (hXmin _ (Finset.mem_univ _))) m
  have hdec : ∀ t, 1 ≤ t → probGT π f (t + m) ≤ (1 - ε) * probGT π f t :=
    MTPAux6f.decay π hπ f hf m ε hεt hgood
  refine MTPAux6f.expTau_lt_top π hπ f hf m hm1 (1 - ε) ?_ hdec
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε0
