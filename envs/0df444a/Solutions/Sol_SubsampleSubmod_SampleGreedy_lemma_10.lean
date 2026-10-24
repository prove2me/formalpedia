-- Prove2me | solution 1 for SubsampleSubmod.SampleGreedy.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:47:02.273856+00:00
-- url     : https://prove2.me/submissions/c11dbdd0-1126-470b-91a5-75a21660b655

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy.LinearCharge

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

end SubsampleSubmod.SampleGreedy.LinearCharge

open SubsampleSubmod.SampleGreedy SubsampleSubmod.SampleGreedy.LinearCharge

theorem SubsampleSubmod.SampleGreedy.LinearCharge.invariants_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
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

namespace SubsampleSubmod.SampleGreedy.LinearCharge

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

noncomputable def charge {α : Type} [DecidableEq α] (st : Alg2State α) (u : α) : ℝ :=
  (st.Ou u).card - if u ∈ st.Y then 1 else 0

noncomputable def considered {α : Type} [DecidableEq α] (st : Alg2State α) (u : α) : ℝ :=
  if u ∈ st.considered then 1 else 0

theorem stable_fields {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (u : α)
    (hu : u ∉ st.rem) :
    u ∉ (alg2Step f I B st).rem ∧
    (u ∈ (alg2Step f I B st).considered ↔ u ∈ st.considered) ∧
    (alg2Step f I B st).Ou u = st.Ou u ∧
    (u ∈ (alg2Step f I B st).Y ↔ u ∈ st.Y) := by
  classical
  cases hpick : pick f I st.rem st.S with
  | none => simpa only [alg2Step, hpick, and_true] using hu
  | some v =>
    have hv := (greedyInvariant_pick_spec f I st.rem st.S v hpick).1
    have huv : u ≠ v := by intro heq; exact hu (heq ▸ hv)
    simp only [alg2Step, hpick]
    split
    · simp only [Finset.mem_erase, hu, and_false, not_false_eq_true, Finset.mem_insert,
        huv, false_or, Function.update_of_ne huv, true_and]
      split <;> simp [huv]
    · simp [hu, huv]

theorem stable_charge {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (u : α)
    (hu : u ∉ st.rem) : charge (alg2Step f I B st) u = charge st u := by
  have hs := stable_fields f I B st u hu
  simp only [charge, hs.2.2.1, hs.2.2.2]

theorem selected_info {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (u : α)
    (hpick : pick f I st.rem st.S = some u) :
    u ∉ (alg2Step f I B st).rem ∧ u ∈ (alg2Step f I B st).considered := by
  classical
  simp only [alg2Step, hpick]
  split <;> simp

theorem selected_pair {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (q c : ℝ) (hq0 : 0 ≤ q) (hqp : q * ((p : ℝ) - 1) = c) (hqc : 1 - q = c)
    (B C : Finset α) (st : Alg2State α) (u : α)
    (huB : u ∈ B) (huC : u ∉ C) (huY : u ∉ st.Y)
    (hO : I st.O) (hSO : st.S ⊆ st.O) (hpick : pick f I st.rem st.S = some u) :
    q * charge (alg2Step f I B st) u + (1 - q) * charge (alg2Step f I C st) u ≤ c := by
  classical
  have hIS := (greedyInvariant_pick_spec f I st.rem st.S u hpick).2.2
  by_cases huO : u ∈ st.O
  · have hMin : minRemoval I st.O (insert u st.S) = ∅ :=
      minRemoval_of_independent I st.O (insert u st.S) hO
    simp [charge, alg2Step, hpick, huB, huC, huY, huO, hMin, hqc]
  · have hc := repair_card I p hI hext st.O st.S hO hSO u huO hIS
    have hacc : charge (alg2Step f I B st) u ≤ (p : ℝ) - 1 := by
      simp only [charge, alg2Step, hpick, if_pos huB, if_neg huO,
        Function.update_self, Finset.mem_insert_self, if_true]
      exact sub_le_sub_right (by exact_mod_cast hc) 1
    have hrej : charge (alg2Step f I C st) u = 0 := by
      simp [charge, alg2Step, hpick, huC, huO, huY]
    rw [hrej, mul_zero, add_zero]
    exact (mul_le_mul_of_nonneg_left hacc hq0).trans_eq hqp

def Paired {α : Type} [DecidableEq α] (q c : ℝ) (u : α)
    (st₁ st₀ : Alg2State α) : Prop :=
  (st₁ = st₀ ∧ u ∉ st₀.considered ∧ st₀.Ou u = ∅ ∧ u ∉ st₀.Y) ∨
  (u ∉ st₁.rem ∧ u ∉ st₀.rem ∧ u ∈ st₁.considered ∧ u ∈ st₀.considered ∧
    q * charge st₁ u + (1 - q) * charge st₀ u ≤ c)

theorem paired_step {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (q c : ℝ) (hq0 : 0 ≤ q) (hqp : q * ((p : ℝ) - 1) = c) (hqc : 1 - q = c)
    (B C : Finset α) (u : α) (huB : u ∈ B) (huC : u ∉ C)
    (hBC : ∀ v, v ≠ u → (v ∈ B ↔ v ∈ C)) (st₁ st₀ : Alg2State α)
    (hO : I st₁.O) (hSO : st₁.S ⊆ st₁.O) (h : Paired q c u st₁ st₀) :
    Paired q c u (alg2Step f I B st₁) (alg2Step f I C st₀) := by
  classical
  rcases h with ⟨heq, huc, hOu, hY⟩ | ⟨hr₁, hr₀, hc₁, hc₀, hb⟩
  · subst st₀
    cases hpick : pick f I st₁.rem st₁.S with
    | none =>
      left
      simpa only [alg2Step, hpick] using
        And.intro (rfl : st₁ = st₁) (And.intro huc (And.intro hOu hY))
    | some v =>
      by_cases hv : v = u
      · subst v
        have hs₁ := selected_info f I B st₁ u hpick
        have hs₀ := selected_info f I C st₁ u hpick
        exact Or.inr ⟨hs₁.1, hs₀.1, hs₁.2, hs₀.2,
          selected_pair f I p hI hext q c hq0 hqp hqc B C st₁ u huB huC hY hO hSO hpick⟩
      · have huv : u ≠ v := Ne.symm hv
        left
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [alg2Step, hpick, hBC v hv]
        · simp only [alg2Step, hpick]
          split <;> simp [huc, huv]
        · simp only [alg2Step, hpick]
          split <;> simp [hOu, huv]
        · simp only [alg2Step, hpick]
          split
          · split <;> simp [hY, huv]
          · exact hY
  · have hs₁ := stable_fields f I B st₁ u hr₁
    have hs₀ := stable_fields f I C st₀ u hr₀
    right
    refine ⟨hs₁.1, hs₀.1, hs₁.2.1.mpr hc₁, hs₀.2.1.mpr hc₀, ?_⟩
    rwa [stable_charge f I B st₁ u hr₁, stable_charge f I C st₀ u hr₀]

theorem paired_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (q c : ℝ) (hq0 : 0 ≤ q) (hqp : q * ((p : ℝ) - 1) = c) (hqc : 1 - q = c)
    (T : Finset α) (hT : I T) (B C : Finset α) (u : α)
    (huB : u ∈ B) (huC : u ∉ C) (hBC : ∀ v, v ≠ u → (v ∈ B ↔ v ∈ C)) (j : ℕ) :
    Paired q c u ((alg2Step f I B)^[j] (alg2Init T))
      ((alg2Step f I C)^[j] (alg2Init T)) := by
  induction j with
  | zero => left; simp [alg2Init]
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hinv := invariants_run f I hI T hT B j
    exact paired_step f I p hI hext q c hq0 hqp hqc B C u huB huC hBC
      _ _ hinv.1 hinv.2.1 ih

theorem paired_final {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hI : IsIndepSystem I) (hext : IsPExtendible p I)
    (q c : ℝ) (hq0 : 0 ≤ q) (hqp : q * ((p : ℝ) - 1) = c) (hqc : 1 - q = c)
    (T : Finset α) (hT : I T) (B : Finset α) (u : α) (hu : u ∉ B) :
    considered (alg2 f I T (insert u B)) u = considered (alg2 f I T B) u ∧
    q * charge (alg2 f I T (insert u B)) u +
      (1 - q) * charge (alg2 f I T B) u ≤ c * considered (alg2 f I T B) u := by
  classical
  have hBC : ∀ v, v ≠ u → (v ∈ insert u B ↔ v ∈ B) := by
    intro v hv
    simp [hv]
  have h := paired_run f I p hI hext q c hq0 hqp hqc T hT (insert u B) B u
    (Finset.mem_insert_self _ _) hu hBC (Fintype.card α)
  change Paired q c u (alg2 f I T (insert u B)) (alg2 f I T B) at h
  rcases h with ⟨heq, huc, hOu, hY⟩ | ⟨_, _, hc₁, hc₀, hb⟩
  · rw [heq]
    simp [considered, charge, huc, hOu, hY]
  · simp only [considered, if_pos hc₁, if_pos hc₀, mul_one]
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

end SubsampleSubmod.SampleGreedy.LinearCharge

theorem solution {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (p : ℕ) (hp : 1 ≤ p) (hI : IsIndepSystem I)
    (hext : IsPExtendible p I) (T : Finset α) (hT : I T) (u : α) :
    E2 (1 / (p : ℝ)) f I T
        (fun st => ((st.Ou u).card : ℝ) - (if u ∈ st.Y then (1 : ℝ) else 0)) ≤
      (((p : ℝ) - 1) / (p : ℝ)) *
        E2 (1 / (p : ℝ)) f I T (fun st => if u ∈ st.considered then (1 : ℝ) else 0) := by
  classical
  let q : ℝ := 1 / (p : ℝ)
  let c : ℝ := ((p : ℝ) - 1) / (p : ℝ)
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hq0 : 0 ≤ q := (one_div_pos.mpr hp0).le
  have hq1 : q ≤ 1 := (div_le_one hp0).mpr hpR
  have hqp : q * ((p : ℝ) - 1) = c := by dsimp only [q, c]; ring
  have hqc : 1 - q = c := by
    dsimp only [q, c]
    field_simp
  have h := weighted_pairing q c hq0 hq1
    (fun B => charge (alg2 f I T B) u) (fun B => considered (alg2 f I T B) u) u
    (fun B hu => paired_final f I p hI hext q c hq0 hqp hqc T hT B u hu)
  simpa only [q, c, E2, charge, considered] using h
