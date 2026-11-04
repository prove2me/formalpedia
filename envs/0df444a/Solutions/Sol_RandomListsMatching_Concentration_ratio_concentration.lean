-- Prove2me | solution 1 for RandomListsMatching.Concentration.ratio_concentration
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T04:10:53.795367+00:00
-- url     : https://prove2.me/submissions/fc572224-7775-44d9-b14e-452e5a844256

import Mathlib
import Definitions.Def_RandomListsMatching_Concentration_Setting
import Theorems.Thm_RandomListsMatching_Concentration_lemma1_alg_lower_tail
import Theorems.Thm_RandomListsMatching_Concentration_lemma2_opt_upper_tail

open MeasureTheory RandomListsMatching.Concentration

theorem solution {A I X : Type} [DecidableEq A] [Fintype A] (E : Finset (A × I))
    [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (typ : X → I) (lst : X → List A)
    (hint : ListsInterested E typ lst) (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    1 - 2 * Real.exp (-2 * (n : ℝ) * ε ^ 2) ≤
      (arrivalLaw ν n).real
        {ω | expALG ν lst n / expOPT ν E typ n - 2 * ε / (expOPT ν E typ n / (n : ℝ) + ε) ≤
          (ALG lst ω : ℝ) / (OPT E typ ω : ℝ)} := by
  classical
  -- Step 1: ALG ≤ OPT pointwise (the greedy assignment is a realization matching).
  have key : ∀ (ls : Fin n → List A) (τ : Fin n → I),
      (∀ t, ∀ a ∈ ls t, (a, τ t) ∈ E) → algValue ls ≤ optValue E τ := by
    intro ls τ hls
    let M : Fin n → Option A := fun t =>
      (ls t).find? (fun a => decide (a ∉ matchedAfter ls t.val))
    have hsucc : ∀ t : Fin n, matchedAfter ls (t.val + 1) =
        greedyStep (matchedAfter ls t.val) (ls t) := by
      intro t; simp [matchedAfter, t.isLt]
    have hstep : ∀ j, matchedAfter ls j ⊆ matchedAfter ls (j + 1) := by
      intro j
      by_cases h : j < n
      · rw [show matchedAfter ls (j+1) = greedyStep (matchedAfter ls j) (ls ⟨j, h⟩) by
          simp [matchedAfter, h]]
        unfold greedyStep
        split
        · exact Finset.subset_insert _ _
        · exact le_rfl
      · simp [matchedAfter, h]
    have hmono : ∀ s t, s ≤ t → matchedAfter ls s ⊆ matchedAfter ls t := by
      intro s t hst
      induction t, hst using Nat.le_induction with
      | base => exact le_rfl
      | succ k _ ih => exact ih.trans (hstep k)
    have hMsome : ∀ t a, M t = some a →
        a ∉ matchedAfter ls t.val ∧ a ∈ matchedAfter ls (t.val + 1) ∧ a ∈ ls t := by
      intro t a h
      have h1 := List.find?_some h
      have h2 := List.mem_of_find?_eq_some h
      simp only [decide_eq_true_eq] at h1
      refine ⟨h1, ?_, h2⟩
      rw [hsucc t]
      unfold greedyStep
      have : (ls t).find? (fun a => decide (a ∉ matchedAfter ls t.val)) = some a := h
      rw [this]
      exact Finset.mem_insert_self _ _
    have hMat : IsRealizationMatching E τ M := by
      refine ⟨fun t a h => hls t a (hMsome t a h).2.2, ?_⟩
      intro s t a hs ht
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact (hMsome t a ht).1 (hmono _ _ (Nat.succ_le_of_lt hlt) (hMsome s a hs).2.1)
      · exact (hMsome s a hs).1 (hmono _ _ (Nat.succ_le_of_lt hlt) (hMsome t a ht).2.1)
    let f : ℕ → ℕ := fun i => if h : i < n then (if (M ⟨i, h⟩).isSome then 1 else 0) else 0
    have hcard : ∀ j, j ≤ n → (matchedAfter ls j).card = ∑ i ∈ Finset.range j, f i := by
      intro j
      induction j with
      | zero => intro _; simp [matchedAfter]
      | succ j ih =>
        intro hj
        have hjn : j < n := hj
        rw [Finset.sum_range_succ, ← ih hjn.le]
        have e := hsucc ⟨j, hjn⟩
        simp only at e
        rw [e]
        simp only [f, hjn, dite_true]
        unfold greedyStep
        cases hM : (ls ⟨j, hjn⟩).find? (fun a => decide (a ∉ matchedAfter ls j)) with
        | none =>
          have : M ⟨j, hjn⟩ = none := hM
          simp [this]
        | some a =>
          have : M ⟨j, hjn⟩ = some a := hM
          have ha := (hMsome ⟨j, hjn⟩ a this).1
          simp only at ha
          simp [this, Finset.card_insert_of_notMem ha]
    have hsize : algValue ls = matchSize M := by
      unfold algValue matchSize
      rw [hcard n le_rfl, Finset.card_filter]
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro t _
      simp [f, t.isLt]
    rw [hsize]
    unfold optValue
    exact Finset.le_sup (f := matchSize) (by simpa using hMat)
  have hAO : ∀ ω : Fin n → X, (ALG lst ω : ℝ) ≤ (OPT E typ ω : ℝ) := by
    intro ω
    exact_mod_cast key (fun j => lst (ω j)) (fun j => typ (ω j)) (fun t a ha => hint (ω t) a ha)
  set μ := arrivalLaw ν n with hμ
  have : IsProbabilityMeasure μ := by
    rw [hμ]; unfold arrivalLaw; infer_instance
  set a := expALG ν lst n with ha
  set b := expOPT ν E typ n with hb
  have hab : a ≤ b := by
    rw [ha, hb]; unfold expALG expOPT
    exact integral_mono Integrable.of_finite Integrable.of_finite hAO
  have ha0 : 0 ≤ a := by
    rw [ha]; unfold expALG; exact integral_nonneg (fun ω => by positivity)
  set N : ℝ := (n : ℝ) * ε with hN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hNpos : 0 < N := mul_pos hnpos hε
  have hrew : 2 * ε / (b / (n : ℝ) + ε) = 2 * N / (b + N) := by
    rw [hN]; field_simp
  -- Step 2: on the good event, the ratio bound holds.
  set S := {ω : Fin n → X | a / b - 2 * ε / (b / (n : ℝ) + ε) ≤
      (ALG lst ω : ℝ) / (OPT E typ ω : ℝ)}
  set B1 := {ω : Fin n → X | (ALG lst ω : ℝ) - a < -((n : ℝ) * ε)}
  set B2 := {ω : Fin n → X | (OPT E typ ω : ℝ) - b > (n : ℝ) * ε}
  have hsub : Sᶜ ⊆ B1 ∪ B2 := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, B1, B2, not_or, not_lt, not_lt] at hc
    apply hω
    simp only [S, Set.mem_setOf_eq]
    rw [hrew]
    obtain ⟨h1, h2⟩ := hc
    set x : ℝ := (ALG lst ω : ℝ)
    set y : ℝ := (OPT E typ ω : ℝ)
    have hx0 : 0 ≤ x := by positivity
    have hxy : x ≤ y := hAO ω
    have h1' : a - N ≤ x := by rw [hN]; linarith
    have h2' : y ≤ b + N := by rw [hN]; linarith
    rcases eq_or_lt_of_le (ha0.trans hab) with hb0 | hbpos
    · rw [← hb0]
      have : (2 * N / (0 + N)) = 2 := by rw [zero_add]; field_simp
      rw [this, div_zero]
      have : 0 ≤ x / y := div_nonneg hx0 (hx0.trans hxy)
      linarith
    · have hbN : 0 < b + N := by linarith
      have step1 : a / b - 2 * N / (b + N) ≤ (a - N) / (b + N) := by
        rw [div_sub_div _ _ hbpos.ne' hbN.ne', div_le_div_iff₀ (mul_pos hbpos hbN) hbN]
        have : 0 ≤ (b - a) * N * (b + N) := by
          apply mul_nonneg (mul_nonneg (by linarith) hNpos.le) hbN.le
        nlinarith
      refine step1.trans ?_
      by_cases haN : a - N ≤ 0
      · exact (div_nonpos_of_nonpos_of_nonneg haN hbN.le).trans
          (div_nonneg hx0 (hx0.trans hxy))
      · push Not at haN
        have hxpos : 0 < x := lt_of_lt_of_le haN h1'
        have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
        calc (a - N) / (b + N) ≤ (a - N) / y :=
              div_le_div_of_nonneg_left haN.le hypos h2'
          _ ≤ x / y := div_le_div_of_nonneg_right h1' hypos.le
  -- Step 3: union bound.
  have hB1 : μ.real B1 ≤ Real.exp (-2 * (n : ℝ) * ε ^ 2) := lemma1_alg_lower_tail ν lst n ε hε
  have hB2 : μ.real B2 ≤ Real.exp (-2 * (n : ℝ) * ε ^ 2) :=
    lemma2_opt_upper_tail E ν typ n ε hε
  have hc : μ.real Sᶜ ≤ μ.real B1 + μ.real B2 :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have huniv : μ.real (Set.univ : Set (Fin n → X)) ≤ μ.real S + μ.real Sᶜ := by
    rw [← Set.union_compl_self S]; exact measureReal_union_le _ _
  rw [probReal_univ] at huniv
  linarith
