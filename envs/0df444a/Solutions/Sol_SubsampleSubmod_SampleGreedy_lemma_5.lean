-- Prove2me | solution 1 for SubsampleSubmod.SampleGreedy.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:05:10.759677+00:00
-- url     : https://prove2.me/submissions/e7fa9693-ce65-4a66-b50a-5e3efc60afd7

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy

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

end SubsampleSubmod.SampleGreedy

open SubsampleSubmod.SampleGreedy

theorem solution {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
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
