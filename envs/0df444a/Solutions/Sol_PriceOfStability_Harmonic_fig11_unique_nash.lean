-- Prove2me | solution 1 for PriceOfStability.Harmonic.fig11_unique_nash
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:21:06.528999+00:00
-- url     : https://prove2.me/submissions/2c5a2136-e3e0-4d55-ac87-f8ac86b9eae0

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_fig11

open CongestionPoA.AsymSum


namespace PriceOfStability.Harmonic

lemma load_pos_iff' {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (e : E) : 0 < load A e ↔ ∃ j, e ∈ A j := by
  unfold load
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  simp

lemma load_eq_one' {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (e : E) (i : ι) (hi : e ∈ A i) (hj : ∀ j, j ≠ i → e ∉ A j) :
    load A e = 1 := by
  unfold load
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h; by_contra hne; exact hj j hne h
  · rintro rfl; exact hi

lemma fig_strat {k : ℕ} {ε : ℝ} (S : Fin k → Finset (Fig11Edge k)) (hS : IsProfile (fig11 k ε) S)
    (j : Fin k) : S j = {Fig11Edge.own j} ∨ S j = {Fig11Edge.common, Fig11Edge.zero j} := by
  have := hS j
  simpa [fig11, fairGame, fig11Strategies] using this

lemma own_not_mem {k : ℕ} {ε : ℝ} (S : Fin k → Finset (Fig11Edge k)) (hS : IsProfile (fig11 k ε) S)
    (i j : Fin k) (h : j ≠ i) : Fig11Edge.own i ∉ S j := by
  rcases fig_strat S hS j with h1 | h1 <;> rw [h1] <;> simp [Ne.symm h]

lemma fig_latency (k : ℕ) (ε : ℝ) (e : Fig11Edge k) (x : ℕ) :
    (fig11 k ε).latency e x = fig11Cost k ε e / x := rfl

lemma fig_strat_mem (k : ℕ) (ε : ℝ) (i : Fin k) :
    {Fig11Edge.own i} ∈ (fig11 k ε).strategies i ∧
      {Fig11Edge.common, Fig11Edge.zero i} ∈ (fig11 k ε).strategies i := by
  simp [fig11, fairGame, fig11Strategies]

lemma cost_own {k : ℕ} {ε : ℝ} (S : Fin k → Finset (Fig11Edge k)) (hS : IsProfile (fig11 k ε) S)
    (i : Fin k) (hi : S i = {Fig11Edge.own i}) :
    cost (fig11 k ε) S i = 1 / ((i : ℕ) + 1 : ℝ) := by
  unfold cost
  rw [hi, Finset.sum_singleton, fig_latency,
    load_eq_one' S _ i (by rw [hi]; simp) (fun j hj => own_not_mem S hS i j hj)]
  simp [fig11Cost]

lemma cost_common {k : ℕ} {ε : ℝ} (S : Fin k → Finset (Fig11Edge k)) (i : Fin k)
    (hi : S i = {Fig11Edge.common, Fig11Edge.zero i}) :
    cost (fig11 k ε) S i = (1 + ε) / (load S Fig11Edge.common : ℝ) := by
  unfold cost
  rw [hi, Finset.sum_pair (by simp), fig_latency, fig_latency]
  simp [fig11Cost]

lemma isProfile_update {k : ℕ} {ε : ℝ} (S : Fin k → Finset (Fig11Edge k))
    (hS : IsProfile (fig11 k ε) S) (i : Fin k) (T : Finset (Fig11Edge k))
    (hT : T ∈ (fig11 k ε).strategies i) : IsProfile (fig11 k ε) (Function.update S i T) := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa using hT
  · rw [Function.update_of_ne hj]; exact hS j

def allOwn (k : ℕ) : Fin k → Finset (Fig11Edge k) := fun i => {Fig11Edge.own i}
def allCommon (k : ℕ) : Fin k → Finset (Fig11Edge k) := fun i => {Fig11Edge.common, Fig11Edge.zero i}

lemma allOwn_profile (k : ℕ) (ε : ℝ) : IsProfile (fig11 k ε) (allOwn k) :=
  fun i => (fig_strat_mem k ε i).1

lemma allCommon_profile (k : ℕ) (ε : ℝ) : IsProfile (fig11 k ε) (allCommon k) :=
  fun i => (fig_strat_mem k ε i).2

lemma allOwn_nash (k : ℕ) (ε : ℝ) (hε : 0 < ε) : IsPureNash (fig11 k ε) (allOwn k) := by
  refine ⟨allOwn_profile k ε, fun i T hT => ?_⟩
  have hP := isProfile_update _ (allOwn_profile k ε) i T hT
  rw [cost_own _ (allOwn_profile k ε) i rfl]
  rcases fig_strat _ hP i with h | h
  · rw [cost_own _ hP i h]
  · rw [Function.update_self] at h
    rw [cost_common _ i (by rw [Function.update_self]; exact h)]
    rw [load_eq_one' _ _ i (by rw [Function.update_self, h]; simp)]
    · have : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      simp only [Nat.cast_one]
      nlinarith
    · intro j hj
      rw [Function.update_of_ne hj]
      simp [allOwn]

lemma nash_eq_allOwn (k : ℕ) (ε : ℝ) (hε : 0 < ε) (S : Fin k → Finset (Fig11Edge k))
    (hS : IsPureNash (fig11 k ε) S) : S = allOwn k := by
  classical
  obtain ⟨hprof, hnash⟩ := hS
  set U := Finset.univ.filter (fun j => Fig11Edge.common ∈ S j) with hU
  by_cases hne : U.Nonempty
  · exfalso
    set i := U.max' hne
    have hiU : i ∈ U := U.max'_mem hne
    have hci : Fig11Edge.common ∈ S i := by simpa [hU] using hiU
    have hSi : S i = {Fig11Edge.common, Fig11Edge.zero i} := by
      rcases fig_strat S hprof i with h | h
      · rw [h] at hci; simp at hci
      · exact h
    have hm : load S Fig11Edge.common = U.card := rfl
    have hsub : U ⊆ Finset.Iic i := fun j hj => Finset.mem_Iic.mpr (U.le_max' j hj)
    have hcard : U.card ≤ (i:ℕ) + 1 := by
      have := Finset.card_le_card hsub
      simpa using this
    have hpos : 1 ≤ U.card := Finset.card_pos.mpr hne
    have h1 := hnash i {Fig11Edge.own i} (fig_strat_mem k ε i).1
    have hP := isProfile_update S hprof i _ (fig_strat_mem k ε i).1
    rw [cost_own _ hP i (by simp), cost_common S i hSi, hm] at h1
    have hmR : (1:ℝ) ≤ U.card := by exact_mod_cast hpos
    have hcR : (U.card:ℝ) ≤ (i:ℕ) + 1 := by exact_mod_cast hcard
    rw [div_le_div_iff₀ (by linarith) (by positivity)] at h1
    nlinarith
  · funext j
    rcases fig_strat S hprof j with h | h
    · exact h
    · exfalso; apply hne; exact ⟨j, by simp [hU, h]⟩

def ownEmb (k : ℕ) : Fin k ↪ Fig11Edge k := ⟨Fig11Edge.own, fun a b h => by cases h; rfl⟩
def zeroEmb (k : ℕ) : Fin k ↪ Fig11Edge k := ⟨Fig11Edge.zero, fun a b h => by cases h; rfl⟩
@[simp] lemma ownEmb_apply (k : ℕ) (a : Fin k) : ownEmb k a = Fig11Edge.own a := rfl
@[simp] lemma zeroEmb_apply (k : ℕ) (a : Fin k) : zeroEmb k a = Fig11Edge.zero a := rfl

lemma design_allOwn (k : ℕ) (ε : ℝ) :
    designCost (fun e _ => fig11Cost k ε e) (allOwn k) = (harmonic k : ℝ) := by
  unfold designCost
  have : Finset.univ.filter (fun e => 0 < load (allOwn k) e)
      = Finset.univ.map (ownEmb k) := by
    ext e
    cases e <;> simp [load_pos_iff', allOwn, ownEmb_apply, zeroEmb_apply]
  rw [this, Finset.sum_map]
  simp only [ownEmb_apply, fig11Cost]
  unfold harmonic
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun i => 1 / ((i:ℝ) + 1))]
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma design_allCommon (k : ℕ) (ε : ℝ) (hk : 1 ≤ k) :
    designCost (fun e _ => fig11Cost k ε e) (allCommon k) = 1 + ε := by
  unfold designCost
  have : Finset.univ.filter (fun e => 0 < load (allCommon k) e)
      = insert Fig11Edge.common (Finset.univ.map (zeroEmb k)) := by
    ext e
    cases e <;> simp [load_pos_iff', allCommon, ownEmb_apply, zeroEmb_apply]
    exact ⟨⟨0, hk⟩⟩
  rw [this, Finset.sum_insert (by simp), Finset.sum_map]
  simp [fig11Cost]

lemma fig_core (k : ℕ) (ε : ℝ) (hk : 1 ≤ k) (hε : 0 < ε) :
    (∃! S, IsPureNash (fig11 k ε) S) ∧
      (∀ S, IsPureNash (fig11 k ε) S →
        designCost (fun e _ => fig11Cost k ε e) S = (harmonic k : ℝ)) ∧
      ∃ P, IsProfile (fig11 k ε) P ∧ designCost (fun e _ => fig11Cost k ε e) P = 1 + ε := by
  refine ⟨⟨allOwn k, allOwn_nash k ε hε, fun S hS => nash_eq_allOwn k ε hε S hS⟩, ?_, ?_⟩
  · intro S hS
    rw [nash_eq_allOwn k ε hε S hS, design_allOwn]
  · exact ⟨allCommon k, allCommon_profile k ε, design_allCommon k ε hk⟩

end PriceOfStability.Harmonic

open PriceOfStability.Harmonic
open CongestionPoA.AsymSum

theorem solution (k : ℕ) (ε : ℝ) (hk : 1 ≤ k) (hε : 0 < ε) :
    (∃! S, IsPureNash (fig11 k ε) S) ∧
      (∀ S, IsPureNash (fig11 k ε) S →
        designCost (fun e _ => fig11Cost k ε e) S = (harmonic k : ℝ)) ∧
      ∃ P, IsProfile (fig11 k ε) P ∧ designCost (fun e _ => fig11Cost k ε e) P = 1 + ε := by
  exact fig_core k ε hk hε
