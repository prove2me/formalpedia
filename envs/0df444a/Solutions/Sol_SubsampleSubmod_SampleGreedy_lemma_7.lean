-- Prove2me | solution 1 for SubsampleSubmod.SampleGreedy.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:40:21.740074+00:00
-- url     : https://prove2.me/submissions/af5e83da-6b2a-4774-aa61-f01113e819f3

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy.ExpectedRemoval

open Finset

/-- A successful greedy choice is a fresh, feasible candidate from the pool. -/
theorem greedyInvariant_pick_spec {α : Type} [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (pool S : Finset α) (u : α)
    (h : pick f I pool S = some u) : u ∈ pool ∧ u ∉ S ∧ I (insert u S) := by
  classical
  unfold pick at h
  dsimp only at h
  split at h
  · rename_i hn
    have hmem := Finset.min'_mem _ hn
    have heq := Option.some.inj h
    rw [heq] at hmem
    have hc := (Finset.mem_filter.mp hmem).1
    simp only [cands, Finset.mem_filter] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
  · cases h

/-- A feasible protected subset supplies a witness for the repair operation. -/
theorem greedyInvariant_minRemoval_spec {α : Type} [DecidableEq α]
    (I : Finset α → Prop) (O S : Finset α) (hSO : S ⊆ O) (hS : I S) :
    minRemoval I O S ⊆ O \ S ∧ I (O \ minRemoval I O S) := by
  classical
  have hex : ((O \ S).powerset.filter (fun X => I (O \ X))).Nonempty := by
    refine ⟨O \ S, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, by rwa [Finset.sdiff_sdiff_eq_self hSO]⟩
  unfold minRemoval
  rw [dif_pos hex]
  have hm := (Classical.choose_spec (Finset.exists_min_image _ Finset.card hex)).1
  simpa only [Finset.mem_filter, Finset.mem_powerset] using hm

/-- Each Algorithm 2 step preserves the three invariants of Lemma 5. -/
theorem greedyInvariant_step {α : Type} [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (hI : IsIndepSystem I)
    (B : Finset α) (st : Alg2State α)
    (hO : I st.O) (hSO : st.S ⊆ st.O)
    (hFresh : ∀ v ∈ st.O \ st.S, v ∉ st.considered) :
    I (alg2Step f I B st).O ∧
    (alg2Step f I B st).S ⊆ (alg2Step f I B st).O ∧
    ∀ v ∈ (alg2Step f I B st).O \ (alg2Step f I B st).S,
      v ∉ (alg2Step f I B st).considered := by
  classical
  cases hp : pick f I st.rem st.S with
  | none => simpa only [alg2Step, hp] using And.intro hO (And.intro hSO hFresh)
  | some u =>
    obtain ⟨_, huS, hIS⟩ := greedyInvariant_pick_spec f I st.rem st.S u hp
    by_cases huB : u ∈ B
    · have hSSOO : insert u st.S ⊆ insert u st.O := Finset.insert_subset_insert u hSO
      obtain ⟨hX, hIX⟩ :=
        greedyInvariant_minRemoval_spec I (insert u st.O) (insert u st.S) hSSOO hIS
      simp only [alg2Step, hp, if_pos huB]
      refine ⟨hIX, ?_, ?_⟩
      · intro v hvS
        refine Finset.mem_sdiff.mpr ⟨hSSOO hvS, ?_⟩
        intro hvX
        exact (Finset.mem_sdiff.mp (hX hvX)).2 hvS
      · intro v hvO hvC
        have hvO' := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hvO).1).1
        have hvnS' := (Finset.mem_sdiff.mp hvO).2
        have hvne : v ≠ u := by
          intro heq
          apply hvnS'
          simp only [heq, Finset.mem_insert_self]
        have hvOold : v ∈ st.O := (Finset.mem_insert.mp hvO').resolve_left hvne
        have hvnSold : v ∉ st.S := fun hv => hvnS' (Finset.mem_insert_of_mem hv)
        have hvnC := hFresh v (Finset.mem_sdiff.mpr ⟨hvOold, hvnSold⟩)
        exact hvnC ((Finset.mem_insert.mp hvC).resolve_left hvne)
    · let X : Finset α := if u ∈ st.O then {u} else ∅
      have hX : X ⊆ {u} := by
        dsimp only [X]
        split <;> simp
      have huRemoved : u ∉ st.O \ X := by
        by_cases huO : u ∈ st.O <;> simp [X, huO]
      simp only [alg2Step, hp, if_neg huB]
      change I (st.O \ X) ∧ st.S ⊆ st.O \ X ∧
        ∀ v ∈ (st.O \ X) \ st.S, v ∉ insert u st.considered
      refine ⟨hI.2 _ _ Finset.sdiff_subset hO, ?_, ?_⟩
      · intro v hvS
        refine Finset.mem_sdiff.mpr ⟨hSO hvS, ?_⟩
        intro hvX
        have hvu : v = u := Finset.mem_singleton.mp (hX hvX)
        exact huS (hvu ▸ hvS)
      · intro v hvO hvC
        have hvOX := (Finset.mem_sdiff.mp hvO).1
        have hvne : v ≠ u := fun heq => huRemoved (heq ▸ hvOX)
        have hvOld : v ∈ st.O \ st.S := Finset.mem_sdiff.mpr
          ⟨(Finset.mem_sdiff.mp hvOX).1, (Finset.mem_sdiff.mp hvO).2⟩
        exact hFresh v hvOld ((Finset.mem_insert.mp hvC).resolve_left hvne)

end SubsampleSubmod.SampleGreedy.ExpectedRemoval

open SubsampleSubmod.SampleGreedy SubsampleSubmod.SampleGreedy.ExpectedRemoval

theorem SubsampleSubmod.SampleGreedy.ExpectedRemoval.invariants_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hI : IsIndepSystem I) (T : Finset α) (hT : I T) (B : Finset α)
    (j : ℕ) :
    I ((alg2Step f I B)^[j] (alg2Init T)).O ∧
    ((alg2Step f I B)^[j] (alg2Init T)).S ⊆ ((alg2Step f I B)^[j] (alg2Init T)).O ∧
    ∀ v ∈ ((alg2Step f I B)^[j] (alg2Init T)).O \ ((alg2Step f I B)^[j] (alg2Init T)).S,
      v ∉ ((alg2Step f I B)^[j] (alg2Init T)).considered := by
  induction j with
  | zero => simpa [alg2Init] using hT
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact greedyInvariant_step f I hI B _ ih.1 ih.2.1 ih.2.2

namespace SubsampleSubmod.SampleGreedy.ExpectedRemoval

open Finset

theorem minRemoval_le {α : Type} [DecidableEq α]
    (I : Finset α → Prop) (O S X : Finset α)
    (hX : X ⊆ O \ S) (hIX : I (O \ X)) : (minRemoval I O S).card ≤ X.card := by
  classical
  have hxmem : X ∈ (O \ S).powerset.filter (fun X => I (O \ X)) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hX, hIX⟩
  have hn : ((O \ S).powerset.filter (fun X => I (O \ X))).Nonempty := ⟨X, hxmem⟩
  unfold minRemoval
  rw [dif_pos hn]
  exact (Classical.choose_spec (Finset.exists_min_image _ Finset.card hn)).2 X hxmem

theorem minRemoval_of_independent {α : Type} [DecidableEq α]
    (I : Finset α → Prop) (O S : Finset α) (hO : I O) : minRemoval I O S = ∅ := by
  have h := minRemoval_le I O S ∅ (Finset.empty_subset _) (by simpa using hO)
  exact Finset.card_eq_zero.mp (by simpa using h)

theorem repair_card {α : Type} [LinearOrder α]
    (I : Finset α → Prop) (p : ℕ) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (O S : Finset α) (hO : I O) (hSO : S ⊆ O) (u : α)
    (huO : u ∉ O) (hIS : I (insert u S)) :
    (minRemoval I (insert u O) (insert u S)).card ≤ p := by
  classical
  have huS : u ∉ S := fun hu => huO (hSO hu)
  obtain ⟨X, hXO, hcard, hIX⟩ := hext S O u (hI.2 _ _ hSO hO) hO hSO huS hIS
  have huX : u ∉ X := fun hu => huO (Finset.mem_sdiff.mp (hXO hu)).1
  have hsub : X ⊆ insert u O \ insert u S := by
    intro v hv
    obtain ⟨hvO, hvS⟩ := Finset.mem_sdiff.mp (hXO hv)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem hvO, ?_⟩
    intro hins
    rcases Finset.mem_insert.mp hins with heq | hvS'
    · exact huO (heq ▸ hvO)
    · exact hvS hvS'
  have heq : insert u O \ X = insert u (O \ X) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    aesop
  exact (minRemoval_le I (insert u O) (insert u S) X hsub (by rwa [heq])).trans hcard

noncomputable def charge {α : Type} [DecidableEq α]
    (f : Finset α → ℝ) (st : Alg2State α) (u : α) : ℝ :=
  ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)

noncomputable def record {α : Type} [DecidableEq α]
    (f : Finset α → ℝ) (st : Alg2State α) (u : α) : ℝ :=
  if u ∈ st.considered then marg f u (st.Su u) else 0

theorem pick_positive {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (u : α)
    (h : pick f I pool S = some u) : 0 < marg f u S := by
  classical
  unfold pick at h
  dsimp only at h
  split at h
  · rename_i hn
    have hmem := Finset.min'_mem _ hn
    rw [Option.some.inj h] at hmem
    have hc := (Finset.mem_filter.mp hmem).1
    exact (Finset.mem_filter.mp hc).2.2.2
  · cases h

theorem step_S_mono {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) :
    st.S ⊆ (alg2Step f I B st).S := by
  classical
  unfold alg2Step
  split
  · exact Finset.Subset.refl _
  · split
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _

theorem stable_fields {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (u : α)
    (hu : u ∉ st.rem) :
    u ∉ (alg2Step f I B st).rem ∧
    (u ∈ (alg2Step f I B st).considered ↔ u ∈ st.considered) ∧
    (alg2Step f I B st).Ou u = st.Ou u ∧
    (alg2Step f I B st).Su u = st.Su u := by
  classical
  cases hp : pick f I st.rem st.S with
  | none => simpa only [alg2Step, hp, and_true] using hu
  | some v =>
    have hv := (greedyInvariant_pick_spec f I st.rem st.S v hp).1
    have huv : u ≠ v := by intro heq; exact hu (heq ▸ hv)
    simp only [alg2Step, hp]
    split <;> simp [hu, huv]

theorem charge_decreases {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (u : α)
    (hu : u ∉ st.rem) (hm : 0 ≤ marg f u (st.Su u)) :
    charge f (alg2Step f I B st) u ≤ charge f st u := by
  have hs := stable_fields f I B st u hu
  unfold charge
  rw [hs.2.2.1, hs.2.2.2]
  apply mul_le_mul_of_nonneg_right _ hm
  exact_mod_cast Finset.card_le_card
    (Finset.sdiff_subset_sdiff_right _ (step_S_mono f I B st))

theorem selected_info {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (u : α)
    (hpick : pick f I st.rem st.S = some u) :
    u ∉ (alg2Step f I B st).rem ∧ u ∈ (alg2Step f I B st).considered ∧
    (alg2Step f I B st).Su u = st.S := by
  classical
  simp only [alg2Step, hpick]
  split <;> simp

theorem selected_pair {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (q c : ℝ) (hq0 : 0 ≤ q) (hqp : q * (p : ℝ) = c) (hqc : 1 - q = c)
    (B C : Finset α) (st : Alg2State α) (u : α)
    (huB : u ∈ B) (huC : u ∉ C) (hO : I st.O) (hSO : st.S ⊆ st.O)
    (hpick : pick f I st.rem st.S = some u) :
    q * charge f (alg2Step f I B st) u + (1 - q) * charge f (alg2Step f I C st) u ≤
      c * marg f u st.S := by
  classical
  obtain ⟨_, huS, hIS⟩ := greedyInvariant_pick_spec f I st.rem st.S u hpick
  have hm := (pick_positive f I st.rem st.S u hpick).le
  by_cases huO : u ∈ st.O
  · have hMin' : minRemoval I st.O (insert u st.S) = ∅ :=
      minRemoval_of_independent I st.O (insert u st.S) hO
    have hdiff : ({u} : Finset α) \ st.S = {u} := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      aesop
    simp [charge, alg2Step, hpick, huB, huC, huO, hMin', hdiff, hqc]
  · have hc := repair_card I p hI hext st.O st.S hO hSO u huO hIS
    have hcard : (((minRemoval I (insert u st.O) (insert u st.S) \ insert u st.S).card) : ℝ)
        ≤ (p : ℝ) := by
      exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans hc
    have hacc : charge f (alg2Step f I B st) u ≤ (p : ℝ) * marg f u st.S := by
      simpa only [charge, alg2Step, hpick, if_pos huB, Function.update_self] using
        (mul_le_mul_of_nonneg_right hcard hm)
    have hrej : charge f (alg2Step f I C st) u = 0 := by
      simp [charge, alg2Step, hpick, huC, huO]
    rw [hrej, mul_zero, add_zero]
    calc
      _ ≤ q * ((p : ℝ) * marg f u st.S) := mul_le_mul_of_nonneg_left hacc hq0
      _ = c * marg f u st.S := by rw [← mul_assoc, hqp]

def Paired {α : Type} [DecidableEq α] (f : Finset α → ℝ) (q c : ℝ) (u : α)
    (st₁ st₀ : Alg2State α) : Prop :=
  (st₁ = st₀ ∧ u ∉ st₀.considered ∧ st₀.Ou u = ∅) ∨
  (u ∉ st₁.rem ∧ u ∉ st₀.rem ∧ u ∈ st₁.considered ∧ u ∈ st₀.considered ∧
    st₁.Su u = st₀.Su u ∧ 0 ≤ marg f u (st₀.Su u) ∧
    q * charge f st₁ u + (1 - q) * charge f st₀ u ≤ c * marg f u (st₀.Su u))

theorem paired_step {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (q c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hqp : q * (p : ℝ) = c) (hqc : 1 - q = c)
    (B C : Finset α) (u : α) (huB : u ∈ B) (huC : u ∉ C)
    (hBC : ∀ v, v ≠ u → (v ∈ B ↔ v ∈ C)) (st₁ st₀ : Alg2State α)
    (hO : I st₁.O) (hSO : st₁.S ⊆ st₁.O) (h : Paired f q c u st₁ st₀) :
    Paired f q c u (alg2Step f I B st₁) (alg2Step f I C st₀) := by
  classical
  rcases h with ⟨heq, huc, hOu⟩ | ⟨hr₁, hr₀, hc₁, hc₀, hSu, hm, hb⟩
  · subst st₀
    cases hpick : pick f I st₁.rem st₁.S with
    | none =>
      left
      simpa only [alg2Step, hpick] using And.intro (rfl : st₁ = st₁) (And.intro huc hOu)
    | some v =>
      by_cases hv : v = u
      · subst v
        have hs₁ := selected_info f I B st₁ u hpick
        have hs₀ := selected_info f I C st₁ u hpick
        right
        refine ⟨hs₁.1, hs₀.1, hs₁.2.1, hs₀.2.1, ?_, ?_, ?_⟩
        · rw [hs₁.2.2, hs₀.2.2]
        · rw [hs₀.2.2]
          exact (pick_positive f I st₁.rem st₁.S u hpick).le
        · rw [hs₀.2.2]
          exact selected_pair f I p hI hext q c hq0 hqp hqc B C st₁ u huB huC hO hSO hpick
      · have huv : u ≠ v := Ne.symm hv
        left
        refine ⟨?_, ?_, ?_⟩
        · simp only [alg2Step, hpick, hBC v hv]
        · simp only [alg2Step, hpick]
          split <;> simp [huc, huv]
        · simp only [alg2Step, hpick]
          split <;> simp [hOu, huv]
  · have hs₁ := stable_fields f I B st₁ u hr₁
    have hs₀ := stable_fields f I C st₀ u hr₀
    have hdec₁ := charge_decreases f I B st₁ u hr₁ (by rwa [hSu])
    have hdec₀ := charge_decreases f I C st₀ u hr₀ hm
    right
    refine ⟨hs₁.1, hs₀.1, hs₁.2.1.mpr hc₁, hs₀.2.1.mpr hc₀, ?_, ?_, ?_⟩
    · rw [hs₁.2.2.2, hs₀.2.2.2, hSu]
    · rwa [hs₀.2.2.2]
    · rw [hs₀.2.2.2]
      exact (add_le_add (mul_le_mul_of_nonneg_left hdec₁ hq0)
        (mul_le_mul_of_nonneg_left hdec₀ (sub_nonneg.mpr hq1))).trans hb

theorem paired_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (q c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hqp : q * (p : ℝ) = c) (hqc : 1 - q = c)
    (T : Finset α) (hT : I T) (B C : Finset α) (u : α)
    (huB : u ∈ B) (huC : u ∉ C) (hBC : ∀ v, v ≠ u → (v ∈ B ↔ v ∈ C)) (j : ℕ) :
    Paired f q c u ((alg2Step f I B)^[j] (alg2Init T))
      ((alg2Step f I C)^[j] (alg2Init T)) := by
  induction j with
  | zero => left; simp [alg2Init]
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hinv := invariants_run f I hI T hT B j
    exact paired_step f I p hI hext q c hq0 hq1 hqp hqc B C u huB huC hBC
      _ _ hinv.1 hinv.2.1 ih

theorem paired_final {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (q c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hqp : q * (p : ℝ) = c) (hqc : 1 - q = c)
    (T : Finset α) (hT : I T) (B : Finset α) (u : α) (hu : u ∉ B) :
    record f (alg2 f I T (insert u B)) u = record f (alg2 f I T B) u ∧
    q * charge f (alg2 f I T (insert u B)) u +
      (1 - q) * charge f (alg2 f I T B) u ≤ c * record f (alg2 f I T B) u := by
  classical
  have hBC : ∀ v, v ≠ u → (v ∈ insert u B ↔ v ∈ B) := by
    intro v hv
    simp [hv]
  have h := paired_run f I p hI hext q c hq0 hq1 hqp hqc T hT (insert u B) B u
    (Finset.mem_insert_self _ _) hu hBC (Fintype.card α)
  change Paired f q c u (alg2 f I T (insert u B)) (alg2 f I T B) at h
  rcases h with ⟨heq, huc, hOu⟩ | ⟨_, _, hc₁, hc₀, hSu, _, hb⟩
  · rw [heq]
    simp [record, charge, huc, hOu]
  · simp only [record, if_pos hc₁, if_pos hc₀, hSu]
    exact ⟨trivial, hb⟩

theorem split_coin_sum {α : Type} [Fintype α] [DecidableEq α] (u : α)
    (H : Finset α → ℝ) :
    (∑ B : Finset α, H B) =
      (∑ B ∈ ((Finset.univ : Finset α).erase u).powerset, H B) +
      ∑ B ∈ ((Finset.univ : Finset α).erase u).powerset, H (insert u B) := by
  have heq : insert u ((Finset.univ : Finset α).erase u) = Finset.univ :=
    Finset.insert_erase (Finset.mem_univ u)
  calc
    _ = ∑ B ∈ (insert u ((Finset.univ : Finset α).erase u)).powerset, H B := by
      rw [heq, Finset.powerset_univ]
    _ = _ := Finset.sum_powerset_insert (Finset.notMem_erase u Finset.univ) H

theorem weight_pair {α : Type} [Fintype α] [DecidableEq α] (q : ℝ)
    (B : Finset α) (u : α) (hu : u ∉ B) :
    (1 - q) * sampleWeight q (insert u B) = q * sampleWeight q B := by
  have hc : B.card < Fintype.card α := by
    have hs : B ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, by intro heq; exact hu (heq ▸ Finset.mem_univ u)⟩
    simpa only [Finset.card_univ] using Finset.card_lt_card hs
  have hn : Fintype.card α - B.card = (Fintype.card α - (B.card + 1)) + 1 := by omega
  unfold sampleWeight
  rw [Finset.card_insert_of_notMem hu, hn, pow_succ, pow_succ]
  ring

theorem weighted_pairing {α : Type} [Fintype α] [DecidableEq α]
    (q c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (g r : Finset α → ℝ) (u : α)
    (hpair : ∀ B, u ∉ B → r (insert u B) = r B ∧
      q * g (insert u B) + (1 - q) * g B ≤ c * r B) :
    (∑ B : Finset α, sampleWeight q B * g B) ≤
      c * ∑ B : Finset α, sampleWeight q B * r B := by
  classical
  rw [split_coin_sum u (fun B => sampleWeight q B * g B),
    split_coin_sum u (fun B => sampleWeight q B * r B),
    mul_add, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro B hB
  have hu : u ∉ B := fun hu => Finset.notMem_erase u Finset.univ
    ((Finset.mem_powerset.mp hB) hu)
  obtain ⟨hrec, hb⟩ := hpair B hu
  have hw := weight_pair q B u hu
  have hnonneg : 0 ≤ sampleWeight q B + sampleWeight q (insert u B) := by
    apply add_nonneg <;> exact mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.mpr hq1) _)
  have hbound := mul_le_mul_of_nonneg_left hb hnonneg
  rw [hrec]
  nlinarith [congrArg (fun x : ℝ => x * g B) hw,
    congrArg (fun x : ℝ => x * g (insert u B)) hw]

end SubsampleSubmod.SampleGreedy.ExpectedRemoval

theorem solution {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) (T : Finset α) (hT : I T) (u : α) :
    E2 (1 / ((p : ℝ) + 1)) f I T
        (fun st => ((st.Ou u \ st.S).card : ℝ) * marg f u (st.Su u)) ≤
      ((p : ℝ) / ((p : ℝ) + 1)) *
        E2 (1 / ((p : ℝ) + 1)) f I T
          (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) := by
  classical
  let q : ℝ := 1 / ((p : ℝ) + 1)
  let c : ℝ := (p : ℝ) / ((p : ℝ) + 1)
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) + 1 := by linarith
  have hq0 : 0 ≤ q := (one_div_pos.mpr hden).le
  have hq1 : q ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hqp : q * (p : ℝ) = c := by dsimp only [q, c]; ring
  have hqc : 1 - q = c := by
    dsimp only [q, c]
    field_simp
    ring
  have h := weighted_pairing q c hq0 hq1
    (fun B => charge f (alg2 f I T B) u) (fun B => record f (alg2 f I T B) u) u
    (fun B hu => paired_final f I p hI hext q c hq0 hq1 hqp hqc T hT B u hu)
  simpa only [q, c, E2, charge, record, ite_mul, one_mul, zero_mul] using h
