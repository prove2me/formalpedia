-- Prove2me | solution 1 for SubsampleSubmod.SampleGreedy.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:29:29.761955+00:00
-- url     : https://prove2.me/submissions/754e7693-06df-478c-af33-4d44e6cc74b5

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy.ExpectedCharge

open Finset

theorem pick_mem {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (u : α)
    (h : pick f I pool S = some u) : u ∈ pool := by
  classical
  unfold pick at h
  dsimp only at h
  split at h
  · rename_i hn
    have hmem := Finset.min'_mem _ hn
    rw [Option.some.inj h] at hmem
    have hc := (Finset.mem_filter.mp hmem).1
    exact (Finset.mem_filter.mp hc).1
  · cases h

theorem fresh_step {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α)
    (h : ∀ v, v ∈ st.rem ↔ v ∉ st.considered) :
    ∀ v, v ∈ (alg2Step f I B st).rem ↔ v ∉ (alg2Step f I B st).considered := by
  classical
  cases hp : pick f I st.rem st.S with
  | none => simpa only [alg2Step, hp] using h
  | some u =>
    intro v
    have heq : v ∈ st.rem.erase u ↔ v ∉ insert u st.considered := by
      simp only [Finset.mem_erase, Finset.mem_insert, not_or, h]
    simp only [alg2Step, hp]
    split <;> exact heq

theorem fresh_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) (j : ℕ) :
    let st := (alg2Step f I B)^[j] (alg2Init T)
    ∀ v, v ∈ st.rem ↔ v ∉ st.considered := by
  induction j with
  | zero => simp [alg2Init]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact fresh_step f I B _ ih

noncomputable def record {α : Type} [DecidableEq α]
    (f : Finset α → ℝ) (st : Alg2State α) (u : α) : ℝ :=
  if u ∈ st.considered then marg f u (st.Su u) else 0

noncomputable def paid {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (B : Finset α) (st : Alg2State α) : ℝ :=
  ∑ u : α, if u ∈ B then record f st u else 0

theorem selected_rem {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (u : α)
    (hp : pick f I st.rem st.S = some u) :
    (alg2Step f I B st).rem = st.rem.erase u := by
  classical
  simp only [alg2Step, hp]
  split <;> rfl

theorem selected_records {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (u : α)
    (hp : pick f I st.rem st.S = some u) :
    record f (alg2Step f I B st) = Function.update (record f st) u (marg f u st.S) := by
  classical
  funext v
  by_cases hv : v = u
  · subst v
    simp only [alg2Step, hp]
    split <;> simp [record]
  · simp only [alg2Step, hp]
    split <;> simp [record, hv]

theorem paid_update {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (u : α)
    (hp : pick f I st.rem st.S = some u) (huc : u ∉ st.considered) :
    paid f B (alg2Step f I B st) = paid f B st +
      if u ∈ B then marg f u st.S else 0 := by
  classical
  have hu0 : record f st u = 0 := by simp [record, huc]
  have heq : (fun v => if v ∈ B then
      (Function.update (record f st) u (marg f u st.S)) v else 0) =
      (fun v => (if v ∈ B then record f st v else 0) +
        if v = u then (if u ∈ B then marg f u st.S else 0) else 0) := by
    funext v
    by_cases hv : v = u
    · subst v
      simp [hu0]
    · simp [hv]
  unfold paid
  rw [selected_records f I B st u hp, heq, Finset.sum_add_distrib]
  simp

theorem telescope_step {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α)
    (hfresh : ∀ v, v ∈ st.rem ↔ v ∉ st.considered)
    (ht : f st.S = f ∅ + paid f B st) :
    f (alg2Step f I B st).S = f ∅ + paid f B (alg2Step f I B st) := by
  classical
  cases hp : pick f I st.rem st.S with
  | none => simpa only [alg2Step, hp] using ht
  | some u =>
    have huc := (hfresh u).mp (pick_mem f I st.rem st.S u hp)
    rw [paid_update f I B st u hp huc]
    by_cases huB : u ∈ B
    · simp only [alg2Step, hp, if_pos huB]
      unfold marg
      linarith
    · simpa only [alg2Step, hp, if_neg huB, add_zero] using ht

theorem telescope_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) (j : ℕ) :
    let st := (alg2Step f I B)^[j] (alg2Init T)
    f st.S = f ∅ + paid f B st := by
  induction j with
  | zero => simp [alg2Init, paid, record]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact telescope_step f I B _ (fresh_run f I T B j) ih

theorem stable_record {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (u : α)
    (hu : u ∉ st.rem) :
    u ∉ (alg2Step f I B st).rem ∧ record f (alg2Step f I B st) u = record f st u := by
  classical
  cases hp : pick f I st.rem st.S with
  | none => simpa only [alg2Step, hp, and_true] using hu
  | some v =>
    have hv := pick_mem f I st.rem st.S v hp
    have huv : u ≠ v := by intro heq; exact hu (heq ▸ hv)
    rw [selected_rem f I B st v hp, selected_records f I B st v hp]
    exact ⟨fun h => hu (Finset.mem_erase.mp h).2, Function.update_of_ne huv _ _⟩

def Coupled {α : Type} [DecidableEq α] (f : Finset α → ℝ) (u : α)
    (st₁ st₂ : Alg2State α) : Prop :=
  st₁ = st₂ ∨ (u ∉ st₁.rem ∧ u ∉ st₂.rem ∧ record f st₁ u = record f st₂ u)

theorem coupled_step {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B C : Finset α) (u : α)
    (hBC : ∀ v, v ≠ u → (v ∈ B ↔ v ∈ C)) (st₁ st₂ : Alg2State α)
    (h : Coupled f u st₁ st₂) :
    Coupled f u (alg2Step f I B st₁) (alg2Step f I C st₂) := by
  classical
  rcases h with heq | ⟨h₁, h₂, heq⟩
  · subst st₂
    cases hp : pick f I st₁.rem st₁.S with
    | none => exact Or.inl (by simp only [alg2Step, hp])
    | some v =>
      by_cases hv : v = u
      · subst v
        right
        rw [selected_rem f I B st₁ u hp, selected_rem f I C st₁ u hp,
          selected_records f I B st₁ u hp, selected_records f I C st₁ u hp]
        simp
      · left
        simp only [alg2Step, hp, hBC v hv]
  · have hs₁ := stable_record f I B st₁ u h₁
    have hs₂ := stable_record f I C st₂ u h₂
    exact Or.inr ⟨hs₁.1, hs₂.1, hs₁.2.trans (heq.trans hs₂.2.symm)⟩

theorem coupled_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B C : Finset α) (u : α)
    (hBC : ∀ v, v ≠ u → (v ∈ B ↔ v ∈ C)) (j : ℕ) :
    Coupled f u ((alg2Step f I B)^[j] (alg2Init T))
      ((alg2Step f I C)^[j] (alg2Init T)) := by
  induction j with
  | zero => exact Or.inl rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact coupled_step f I B C u hBC _ _ ih

theorem own_coin_independent {α : Type} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (T B : Finset α) (u : α) :
    record f (alg2 f I T (insert u B)) u = record f (alg2 f I T B) u := by
  have hBC : ∀ v, v ≠ u → (v ∈ insert u B ↔ v ∈ B) := by
    intro v hv
    simp only [Finset.mem_insert, hv, false_or]
  have h := coupled_run f I T (insert u B) B u hBC (Fintype.card α)
  rcases h with heq | h
  · exact congrArg (fun st => record f st u) heq
  · exact h.2.2

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

theorem bernoulli_pairing {α : Type} [Fintype α] [DecidableEq α] (q : ℝ)
    (g : Finset α → ℝ) (u : α) (hg : ∀ B, g (insert u B) = g B) :
    (∑ B : Finset α, sampleWeight q B * (if u ∈ B then g B else 0)) =
      q * ∑ B : Finset α, sampleWeight q B * g B := by
  classical
  rw [split_coin_sum u (fun B => sampleWeight q B * (if u ∈ B then g B else 0)),
    split_coin_sum u (fun B => sampleWeight q B * g B)]
  have hzero : (∑ B ∈ ((Finset.univ : Finset α).erase u).powerset,
      sampleWeight q B * (if u ∈ B then g B else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro B hB
    have hu : u ∉ B := fun hu => Finset.notMem_erase u Finset.univ
      ((Finset.mem_powerset.mp hB) hu)
    simp [hu]
  rw [hzero, zero_add, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  have hu : u ∉ B := fun hu => Finset.notMem_erase u Finset.univ
    ((Finset.mem_powerset.mp hB) hu)
  have hw := weight_pair q B u hu
  simp only [Finset.mem_insert_self, if_true, hg]
  nlinarith [congrArg (fun x : ℝ => x * g B) hw]

theorem expectation_identity {α : Type} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (T : Finset α) (q : ℝ) :
    q * (∑ u : α, E2 q f I T (fun st => record f st u)) =
      ∑ B : Finset α, sampleWeight q B * paid f B (alg2 f I T B) := by
  classical
  unfold E2
  rw [Finset.mul_sum]
  simp_rw [← bernoulli_pairing q (fun B => record f (alg2 f I T B) _) _
    (fun B => own_coin_independent f I T B _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  unfold paid
  rw [Finset.mul_sum]

theorem expected_paid_le {α : Type} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (hf0 : ∀ S, 0 ≤ f S)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (T : Finset α) :
    (∑ B : Finset α, sampleWeight q B * paid f B (alg2 f I T B)) ≤
      E2 q f I T (fun st => f st.S) := by
  unfold E2
  apply Finset.sum_le_sum
  intro B _
  have hw : 0 ≤ sampleWeight q B :=
    mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (sub_nonneg.mpr hq1) _)
  apply mul_le_mul_of_nonneg_left _ hw
  have ht := telescope_run f I T B (Fintype.card α)
  change f (alg2 f I T B).S = f ∅ + paid f B (alg2 f I T B) at ht
  linarith [hf0 ∅]

end SubsampleSubmod.SampleGreedy.ExpectedCharge

open SubsampleSubmod.SampleGreedy

theorem solution {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hf0 : ∀ S, 0 ≤ f S) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (T : Finset α) :
    q * ∑ u : α, E2 q f I T
        (fun st => (if u ∈ st.considered then (1 : ℝ) else 0) * marg f u (st.Su u)) ≤
      E2 q f I T (fun st => f st.S) := by
  classical
  have heq := ExpectedCharge.expectation_identity f I T q
  have hle := ExpectedCharge.expected_paid_le f I hf0 q hq0 hq1 T
  have hr : ∀ u : α,
      (fun st : Alg2State α => (if u ∈ st.considered then (1 : ℝ) else 0) *
        marg f u (st.Su u)) = (fun st => ExpectedCharge.record f st u) := by
    intro u
    funext st
    by_cases hu : u ∈ st.considered <;> simp [ExpectedCharge.record, hu]
  simp_rw [hr]
  rw [heq]
  exact hle
