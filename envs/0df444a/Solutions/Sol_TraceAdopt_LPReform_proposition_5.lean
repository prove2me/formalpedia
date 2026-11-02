-- Prove2me | solution 1 for TraceAdopt.LPReform.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:37:12.344858+00:00
-- url     : https://prove2.me/submissions/b813b3ab-b18a-4805-aaa2-e306b474de1c

import Definitions.Def_TraceAdopt_LPReform_BiLP4

namespace TraceAdopt.LPReform

theorem ta_ltm_mem (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) (v : Fin I.n ⊕ Fin I.m) :
    v ∈ ltmStep I S ↔ v ∈ S ∨ (v ∉ S ∧
      match v with
      | Sum.inl i => I.c i ≤ ∑ j ∈ Finset.univ.filter
          (fun j => Sum.inr j ∈ S ∧ i ∈ I.e j), I.r j i
      | Sum.inr j => I.θ j - 1 ≤
          (Finset.univ.filter (fun i => Sum.inl i ∈ S ∧ i ∈ I.e j)).card) := by
  classical
  unfold ltmStep
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · right; refine ⟨h1, ?_⟩
      cases v with
      | inl i => simpa using h2
      | inr j => simpa using h2
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · right; refine ⟨h1, ?_⟩
      cases v with
      | inl i => simpa using h2
      | inr j => simpa using h2

theorem ta_ltm_inl (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) (i : Fin I.n) :
    Sum.inl i ∈ ltmStep I S ↔ Sum.inl i ∈ S ∨ I.c i ≤ ∑ j ∈ Finset.univ.filter
          (fun j => Sum.inr j ∈ S ∧ i ∈ I.e j), I.r j i := by
  rw [ta_ltm_mem]
  tauto

theorem ta_ltm_inr (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) (j : Fin I.m) :
    Sum.inr j ∈ ltmStep I S ↔ Sum.inr j ∈ S ∨ I.θ j - 1 ≤
          (Finset.univ.filter (fun i => Sum.inl i ∈ S ∧ i ∈ I.e j)).card := by
  rw [ta_ltm_mem]
  tauto

theorem ta_step_mem (I : Instance) (S : Finset (Fin I.n)) (i : Fin I.n) :
    i ∈ step I S ↔ i ∈ S ∨ I.c i ≤ ∑ j ∈ Finset.univ.filter
      (fun j => i ∈ I.e j ∧ I.θ j - 1 ≤ (S ∩ I.e j).card), I.r j i := by
  unfold step
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem ta_step_mono (I : Instance) {S U : Finset (Fin I.n)} (h : S ⊆ U) :
    step I S ⊆ step I U := by
  intro i hi
  rw [ta_step_mem] at hi ⊢
  rcases hi with hi | hi
  · exact Or.inl (h hi)
  · right
    refine le_trans hi (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _))
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, le_trans hj.2 (Finset.card_le_card (Finset.inter_subset_inter_right h))⟩

theorem ta_step_ext (I : Instance) (S : Finset (Fin I.n)) : S ⊆ step I S := by
  intro i hi; rw [ta_step_mem]; exact Or.inl hi

theorem ta_ltm_ext (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) : S ⊆ ltmStep I S := by
  intro v hv; rw [ta_ltm_mem]; exact Or.inl hv

theorem ta_iter_step_succ_sub (I : Instance) (S : Finset (Fin I.n)) (t : ℕ) :
    (step I)^[t] S ⊆ (step I)^[t+1] S := by
  rw [Function.iterate_succ_apply']
  exact ta_step_ext I _

theorem ta_iter_ltm_mono (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) {a b : ℕ}
    (h : a ≤ b) : (ltmStep I)^[a] S ⊆ (ltmStep I)^[b] S := by
  induction b with
  | zero => simp at h; subst h; exact le_rfl
  | succ b ih =>
    rcases Nat.of_le_succ h with h | h
    · rw [Function.iterate_succ_apply']
      exact (ih h).trans (ta_ltm_ext I _)
    · rw [h]


theorem ta_iter_step_mono (I : Instance) (S : Finset (Fin I.n)) {a b : ℕ}
    (h : a ≤ b) : (step I)^[a] S ⊆ (step I)^[b] S := by
  induction b with
  | zero => simp at h; subst h; exact le_rfl
  | succ b ih =>
    rcases Nat.of_le_succ h with h | h
    · exact (ih h).trans (ta_iter_step_succ_sub I S b)
    · rw [h]

section P5
variable (I : Instance)

/-- Two-step relation through a supplier. -/
def taR (lFS : Fin I.n → Fin I.m → ℕ) (lSF : Fin I.m → Fin I.n → ℕ) (a b : Fin I.n) : Prop :=
  ∃ j, lFS a j = 1 ∧ lSF j b = 1

theorem taR_trans {s : Fin I.n → ℕ} {lFS : Fin I.n → Fin I.m → ℕ} {lSF : Fin I.m → Fin I.n → ℕ}
    (h : BiLP4Feasible I s lFS lSF) {a b c : Fin I.n}
    (hab : taR I lFS lSF a b) (hbc : taR I lFS lSF b c) : taR I lFS lSF a c := by
  obtain ⟨j, h1, h2⟩ := hab
  obtain ⟨k, h3, h4⟩ := hbc
  refine ⟨k, ?_, h4⟩
  have hc := h.2.2.2.2.1 a k
  have hd := h.2.2.2.2.2 a b j k
  have hb := h.2.1 a k
  omega

theorem taR_irrefl {s : Fin I.n → ℕ} {lFS : Fin I.n → Fin I.m → ℕ} {lSF : Fin I.m → Fin I.n → ℕ}
    (h : BiLP4Feasible I s lFS lSF) (a : Fin I.n) : ¬ taR I lFS lSF a a := by
  rintro ⟨j, h1, h2⟩
  have hc := h.2.2.2.2.1 a j
  omega

open Classical in
theorem taR_rank {s : Fin I.n → ℕ} {lFS : Fin I.n → Fin I.m → ℕ} {lSF : Fin I.m → Fin I.n → ℕ}
    (h : BiLP4Feasible I s lFS lSF) {a b : Fin I.n} (hab : taR I lFS lSF a b) :
    (Finset.univ.filter (fun x => taR I lFS lSF x a)).card <
      (Finset.univ.filter (fun x => taR I lFS lSF x b)).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, by simp [hab], by simp [taR_irrefl I h a]⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact taR_trans I h hx hab

/-- Feasibility of (4) forces full activation. -/
theorem ta_feas_imp (s : Fin I.n → ℕ) (lFS : Fin I.n → Fin I.m → ℕ)
    (lSF : Fin I.m → Fin I.n → ℕ) (h : BiLP4Feasible I s lFS lSF) :
    FullyActivates I (Finset.univ.filter (fun i => s i = 1)) := by
  classical
  set S := Finset.univ.filter (fun i => s i = 1) with hS
  have hmono : Monotone (fun t => (step I)^[t] S) :=
    fun a b hab => ta_iter_step_mono I S hab
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (α := Finset (Fin I.n)) ⟨fun t => (step I)^[t] S, hmono⟩
  set A := (step I)^[N] S with hA
  have hfix : step I A = A := by
    have := hN (N + 1) (by omega)
    simp only [OrderHom.coe_mk] at this
    show step I ((step I)^[N] S) = (step I)^[N] S
    rw [← Function.iterate_succ_apply' (step I) N S]; exact this.symm
  refine ⟨N, ?_⟩
  rw [← hA]
  apply Finset.eq_univ_of_forall
  suffices H : ∀ k, ∀ i, (Finset.univ.filter (fun x => taR I lFS lSF x i)).card = k → i ∈ A by
    intro i; exact H _ i rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro i hk
  by_contra hiA
  have hiS : s i = 0 := by
    have hle := h.1 i
    have : i ∉ S := fun hi => hiA (ta_iter_step_mono I S (Nat.zero_le N) hi)
    simp [hS] at this
    omega
  have h4a := h.2.2.1 i
  rw [hiS, Nat.mul_zero, Nat.add_zero] at h4a
  have hnot : ¬ (I.c i ≤ ∑ j ∈ Finset.univ.filter
      (fun j => i ∈ I.e j ∧ I.θ j - 1 ≤ (A ∩ I.e j).card), I.r j i) := by
    intro hc
    apply hiA
    rw [← hfix, ta_step_mem]
    exact Or.inr hc
  -- find a supplier j pointing to i that is not activated by A
  have hj : ∃ j, i ∈ I.e j ∧ lSF j i = 1 ∧ (A ∩ I.e j).card < I.θ j - 1 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    refine le_trans h4a ?_
    rw [← Finset.filter_filter, Finset.sum_filter (p := fun j => I.θ j - 1 ≤ (A ∩ I.e j).card)]
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hl := (h.2.1 i j).2
    split_ifs with hc
    · calc I.r j i * lSF j i ≤ I.r j i * 1 := Nat.mul_le_mul_left _ hl
        _ = I.r j i := by ring
    · have : lSF j i ≠ 1 := fun h1 => hc (hcon j hj h1)
      have : lSF j i = 0 := by omega
      simp [this]
  obtain ⟨j, hij, hl, hcard⟩ := hj
  have h4b := h.2.2.2.1 j
  have hi' : ∃ i', i' ∈ I.e j ∧ lFS i' j = 1 ∧ i' ∉ A := by
    by_contra hcon
    push Not at hcon
    have : (∑ x ∈ Finset.univ.filter (fun x => x ∈ I.e j), lFS x j) ≤ (A ∩ I.e j).card := by
      have hAe : A ∩ I.e j = Finset.univ.filter (fun x => x ∈ I.e j ∧ x ∈ A) := by
        ext x; simp; tauto
      rw [hAe, Finset.card_filter, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro x _
      have hl := (h.2.1 x j).1
      by_cases hx : x ∈ I.e j
      · by_cases hxA : x ∈ A
        · simp [hx, hxA]; exact hl
        · have : lFS x j ≠ 1 := fun h1 => hxA (hcon x hx h1)
          have : lFS x j = 0 := by omega
          simp [hx, hxA, this]
      · simp [hx]
    omega
  obtain ⟨i', _, hl', hi'A⟩ := hi'
  have hR : taR I lFS lSF i' i := ⟨j, hl', hl⟩
  exact hi'A (ih _ (hk ▸ taR_rank I h hR) i' rfl)

/-- A fully activating seed set yields a feasible solution of (4). -/
theorem ta_imp_feas (S : Finset (Fin I.n)) (hS : FullyActivates I S) (hθ : ∀ j, I.θ j ≤ (I.e j).card) :
    ∃ lFS lSF, BiLP4Feasible I (fun i => if i ∈ S then 1 else 0) lFS lSF := by
  classical
  obtain ⟨T, hT⟩ := hS
  have hex : ∀ i, ∃ t, i ∈ (step I)^[t] S := fun i => ⟨T, by rw [hT]; exact Finset.mem_univ i⟩
  have hexj : ∀ j, ∃ t, I.θ j - 1 ≤ ((step I)^[t] S ∩ I.e j).card := by
    intro j; refine ⟨T, ?_⟩
    rw [hT, Finset.univ_inter]; have := hθ j; omega
  let τ : Fin I.n → ℕ := fun i => Nat.find (hex i)
  let σ : Fin I.m → ℕ := fun j => Nat.find (hexj j)
  have hτ : ∀ i t, i ∈ (step I)^[t] S ↔ τ i ≤ t := by
    intro i t
    constructor
    · intro h; exact Nat.find_min' (hex i) h
    · intro h; exact ta_iter_step_mono I S h (Nat.find_spec (hex i))
  have hσ : ∀ j t, I.θ j - 1 ≤ ((step I)^[t] S ∩ I.e j).card ↔ σ j ≤ t := by
    intro j t
    constructor
    · intro h; exact Nat.find_min' (hexj j) h
    · intro h
      exact le_trans (Nat.find_spec (hexj j)) (Finset.card_le_card
        (Finset.inter_subset_inter_right (ta_iter_step_mono I S h)))
  refine ⟨fun i j => if τ i ≤ σ j then 1 else 0, fun j i => if σ j < τ i then 1 else 0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; dsimp only; split_ifs <;> omega
  · intro i j; dsimp only; constructor <;> split_ifs <;> omega
  · intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp only [hi, if_false, Nat.mul_zero, Nat.add_zero]
      have hτpos : τ i ≠ 0 := by
        intro h0
        have := (hτ i 0).2 (by omega)
        simp at this
        exact hi this
      obtain ⟨t, ht⟩ : ∃ t, τ i = t + 1 := ⟨τ i - 1, by omega⟩
      have hin : i ∈ (step I)^[t+1] S := (hτ i _).2 (le_of_eq ht)
      have hnin : i ∉ (step I)^[t] S := fun h => by have := (hτ i t).1 h; omega
      rw [Function.iterate_succ_apply', ta_step_mem] at hin
      rcases hin with hin | hin
      · exact absurd hin hnin
      refine le_trans hin ?_
      rw [← Finset.filter_filter, Finset.sum_filter (p := fun j => I.θ j - 1 ≤ ((step I)^[t] S ∩ I.e j).card)]
      apply Finset.sum_le_sum
      intro j _
      split_ifs with h1 h2
      · simp
      · exfalso; have := (hσ j t).1 h1; omega
      · exact Nat.zero_le _
      · exact Nat.zero_le _
  · intro j
    have hs := (hσ j (σ j)).2 le_rfl
    refine le_trans hs ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have : (step I)^[σ j] S ∩ I.e j = Finset.univ.filter (fun i => i ∈ I.e j ∧ i ∈ (step I)^[σ j] S) := by
      ext x; simp; tauto
    rw [this, ← Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro x _
    have hτx := hτ x (σ j)
    dsimp only
    split_ifs <;> simp_all
  · intro i j; simp only; split_ifs <;> omega
  · intro i₁ i₂ j₁ j₂; simp only; split_ifs <;> omega

end P5

theorem ta_prop5 (I : Instance) (hI : I.Standing) :
    (∀ s : Fin I.n → ℕ,
      (∃ lFS lSF, BiLP4Feasible I s lFS lSF) ↔
        ∃ S : Finset (Fin I.n), FullyActivates I S ∧
          ∀ i, s i = if i ∈ S then 1 else 0) ∧
    (∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ)
        (lFS : Fin I.n → Fin I.m → ℕ)
        (lSF : Fin I.m → Fin I.n → ℕ),
      BiLP4Feasible I s lFS lSF →
      (∀ (s' : Fin I.n → ℕ)
          (lFS' : Fin I.n → Fin I.m → ℕ)
          (lSF' : Fin I.m → Fin I.n → ℕ),
        BiLP4Feasible I s' lFS' lSF' →
          (∑ i, w i * (s i : ℝ)) ≤ ∑ i, w i * (s' i : ℝ)) →
      FullyActivates I (Finset.univ.filter (fun i => s i = 1)) ∧
      (∑ i, w i * (s i : ℝ)) = OPT I w) := by
  classical
  have hθ : ∀ j, I.θ j ≤ (I.e j).card := fun j => (hI.2.1 j).2
  have hsum : ∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ), (∀ i, s i ≤ 1) →
      (∑ i, w i * (s i : ℝ)) = ∑ i ∈ Finset.univ.filter (fun i => s i = 1), w i := by
    intro w s hs
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    have := hs i
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> simp [h]
  refine ⟨?_, ?_⟩
  · intro s
    constructor
    · rintro ⟨lFS, lSF, h⟩
      refine ⟨_, ta_feas_imp I s lFS lSF h, ?_⟩
      intro i
      have := h.1 i
      by_cases hi : s i = 1 <;> simp [hi] <;> omega
    · rintro ⟨S, hS, hs⟩
      obtain ⟨lFS, lSF, h⟩ := ta_imp_feas I S hS hθ
      refine ⟨lFS, lSF, ?_⟩
      have : s = fun i => if i ∈ S then 1 else 0 := funext hs
      rw [this]; exact h
  · intro w s lFS lSF h hopt
    have hfa := ta_feas_imp I s lFS lSF h
    refine ⟨hfa, ?_⟩
    rw [hsum w s h.1]
    apply le_antisymm
    · unfold OPT
      apply Finset.le_inf'
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      obtain ⟨lFS', lSF', h'⟩ := ta_imp_feas I S hS hθ
      have := hopt _ lFS' lSF' h'
      rw [hsum w s h.1, hsum w _ h'.1] at this
      refine le_trans this (le_of_eq ?_)
      congr 1
      ext i; simp
    · unfold OPT
      apply Finset.inf'_le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hfa

end TraceAdopt.LPReform

open TraceAdopt.LPReform in
theorem solution (I : Instance) (hI : I.Standing) :
    (∀ s : Fin I.n → ℕ,
      (∃ lFS lSF, BiLP4Feasible I s lFS lSF) ↔
        ∃ S : Finset (Fin I.n), FullyActivates I S ∧
          ∀ i, s i = if i ∈ S then 1 else 0) ∧
    (∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ)
        (lFS : Fin I.n → Fin I.m → ℕ)
        (lSF : Fin I.m → Fin I.n → ℕ),
      BiLP4Feasible I s lFS lSF →
      (∀ (s' : Fin I.n → ℕ)
          (lFS' : Fin I.n → Fin I.m → ℕ)
          (lSF' : Fin I.m → Fin I.n → ℕ),
        BiLP4Feasible I s' lFS' lSF' →
          (∑ i, w i * (s i : ℝ)) ≤ ∑ i, w i * (s' i : ℝ)) →
      FullyActivates I (Finset.univ.filter (fun i => s i = 1)) ∧
      (∑ i, w i * (s i : ℝ)) = OPT I w) :=
  ta_prop5 I hI
