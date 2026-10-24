-- Prove2me | solution 1 for SubsampleSubmod.SampleGreedy.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:34:13.18277+00:00
-- url     : https://prove2.me/submissions/92d8f0e6-1d31-43b2-80c6-1a403b3bd09d

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy.EquivalenceProof

open Finset

/- The pick-membership and Algorithm 2 termination helpers are copied from the
checked greedy-pathwise proof in this sprint, with full proof bodies included.
No registered theorem or unproved assumption is imported. -/

theorem local_pick_spec {α : Type} [LinearOrder α]
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

theorem rem_measure {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) (j : ℕ) :
    let st := (alg2Step f I B)^[j] (alg2Init T)
    pick f I st.rem st.S = none ∨ st.rem.card + j ≤ Fintype.card α := by
  induction j with
  | zero => exact Or.inr (by simp [alg2Init])
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    dsimp only at ih ⊢
    let st := (alg2Step f I B)^[j] (alg2Init T)
    change pick f I (alg2Step f I B st).rem (alg2Step f I B st).S = none ∨
      (alg2Step f I B st).rem.card + (j + 1) ≤ Fintype.card α
    change pick f I st.rem st.S = none ∨ st.rem.card + j ≤ Fintype.card α at ih
    cases hp : pick f I st.rem st.S with
    | none => exact Or.inl (by simp only [alg2Step, hp])
    | some u =>
      have hj := ih.resolve_left (by simp [hp])
      have hu := (local_pick_spec f I st.rem st.S u hp).1
      have hc := Finset.card_erase_add_one hu
      right
      simp only [alg2Step, hp]
      split <;> dsimp only <;> omega

theorem terminated {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) :
    pick f I (alg2 f I T B).rem (alg2 f I T B).S = none := by
  have hm := rem_measure f I T B (Fintype.card α)
  change pick f I (alg2 f I T B).rem (alg2 f I T B).S = none ∨
    (alg2 f I T B).rem.card + Fintype.card α ≤ Fintype.card α at hm
  rcases hm with hp | hcard
  · exact hp
  · cases hp : pick f I (alg2 f I T B).rem (alg2 f I T B).S with
    | none => rfl
    | some u =>
      have hu := (local_pick_spec f I _ _ u hp).1
      have hpos : 0 < (alg2 f I T B).rem.card := Finset.card_pos.mpr ⟨u, hu⟩
      omega


theorem pick_spec {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (u : α)
    (hp : pick f I pool S = some u) :
    u ∈ cands f I pool S ∧
    (∀ v ∈ cands f I pool S, marg f v S ≤ marg f u S) ∧
    (∀ v ∈ cands f I pool S, marg f v S = marg f u S → u ≤ v) := by
  classical
  unfold pick at hp
  dsimp only at hp
  split at hp
  · rename_i hn
    have hm := Finset.min'_mem _ hn
    have heq := Option.some.inj hp
    rw [heq] at hm
    obtain ⟨hu, hmax⟩ := Finset.mem_filter.mp hm
    refine ⟨hu, hmax, ?_⟩
    intro v hv he
    rw [← heq]
    apply Finset.min'_le
    exact Finset.mem_filter.mpr ⟨hv, fun w hw => (hmax w hw).trans_eq he.symm⟩
  · cases hp

theorem pick_of_spec {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (u : α)
    (hu : u ∈ cands f I pool S)
    (hmax : ∀ v ∈ cands f I pool S, marg f v S ≤ marg f u S)
    (hmin : ∀ v ∈ cands f I pool S, marg f v S = marg f u S → u ≤ v) :
    pick f I pool S = some u := by
  classical
  have hmem : u ∈ (cands f I pool S).filter
      (fun u => ∀ v ∈ cands f I pool S, marg f v S ≤ marg f u S) :=
    Finset.mem_filter.mpr ⟨hu, hmax⟩
  unfold pick
  dsimp only
  rw [dif_pos ⟨u, hmem⟩]
  congr 1
  apply (Finset.min'_eq_iff _ _ u).mpr
  refine ⟨hmem, ?_⟩
  intro v hv
  obtain ⟨hv, hvm⟩ := Finset.mem_filter.mp hv
  exact hmin v hv (le_antisymm (hmax v hv) (hvm u hu))

theorem pick_restrict {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (small big S : Finset α) (u : α)
    (hsub : cands f I small S ⊆ cands f I big S)
    (hu : u ∈ small) (hp : pick f I big S = some u) : pick f I small S = some u := by
  obtain ⟨hc, hmax, hmin⟩ := pick_spec f I big S u hp
  have hsmall : u ∈ cands f I small S := by
    classical
    exact Finset.mem_filter.mpr ⟨hu, (Finset.mem_filter.mp hc).2⟩
  exact pick_of_spec f I small S u hsmall
    (fun v hv => hmax v (hsub hv)) (fun v hv => hmin v (hsub hv))

theorem cands_empty_of_pick_none {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (hp : pick f I pool S = none) :
    cands f I pool S = ∅ := by
  classical
  by_contra hc
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image (cands f I pool S)
    (fun u => marg f u S) (Finset.nonempty_iff_ne_empty.mpr hc)
  have hM : ((cands f I pool S).filter
      (fun u => ∀ v ∈ cands f I pool S, marg f v S ≤ marg f u S)).Nonempty :=
    ⟨u, Finset.mem_filter.mpr ⟨hu, hmax⟩⟩
  unfold pick at hp
  dsimp only at hp
  rw [dif_pos hM] at hp
  cases hp

theorem pick_none_of_cands_empty {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (hc : cands f I pool S = ∅) :
    pick f I pool S = none := by
  classical
  simp [pick, hc]

theorem greedy_measure {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (j : ℕ) :
    let S' := (greedyStep f I pool)^[j] S
    pick f I pool S' = none ∨ j ≤ S'.card := by
  induction j with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    dsimp only at ih ⊢
    let S' := (greedyStep f I pool)^[j] S
    change pick f I pool (greedyStep f I pool S') = none ∨
      j + 1 ≤ (greedyStep f I pool S').card
    change pick f I pool S' = none ∨ j ≤ S'.card at ih
    cases hp : pick f I pool S' with
    | none => exact Or.inl (by simp only [greedyStep, hp])
    | some u =>
      have hj := ih.resolve_left (by simp [hp])
      have hu := (local_pick_spec f I pool S' u hp).2.1
      right
      simp only [greedyStep, hp, Finset.card_insert_of_notMem hu]
      omega

theorem greedy_terminated {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) :
    pick f I pool ((greedyStep f I pool)^[Fintype.card α] S) = none := by
  have hm := greedy_measure f I pool S (Fintype.card α)
  dsimp only at hm
  rcases hm with hp | hc
  · exact hp
  · cases hp : pick f I pool ((greedyStep f I pool)^[Fintype.card α] S) with
    | none => rfl
    | some u =>
      have hu := (local_pick_spec f I pool _ u hp).2.1
      have hcard := Finset.card_insert_of_notMem hu
      have hbound := Finset.card_le_univ (insert u ((greedyStep f I pool)^[Fintype.card α] S))
      omega

noncomputable def finish {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) : Finset α :=
  (greedyStep f I pool)^[Fintype.card α] S

theorem finish_step {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) :
    finish f I pool (greedyStep f I pool S) = finish f I pool S := by
  unfold finish
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  simp only [greedyStep, greedy_terminated]

theorem finish_of_none {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (hp : pick f I pool S = none) :
    finish f I pool S = S := by
  have hs : greedyStep f I pool S = S := by simp [greedyStep, hp]
  exact Function.IsFixedPt.iterate hs _

def Cover {α : Type} [DecidableEq α] (B : Finset α) (st : Alg2State α) : Prop :=
  B ⊆ st.rem ∪ st.S

theorem cover_step {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (hc : Cover B st) :
    Cover B (alg2Step f I B st) := by
  classical
  cases hp : pick f I st.rem st.S with
  | none => simpa only [alg2Step, hp] using hc
  | some u =>
    by_cases hu : u ∈ B
    · simp only [alg2Step, hp, if_pos hu, Cover]
      intro v hv
      have hv' := hc hv
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert] at hv' ⊢
      by_cases h : v = u <;> aesop
    · simp only [alg2Step, hp, if_neg hu, Cover]
      intro v hv
      have hv' := hc hv
      have hne : v ≠ u := by intro h; exact hu (h ▸ hv)
      simp only [Finset.mem_union, Finset.mem_erase] at hv' ⊢
      aesop

theorem cover_cands {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (hc : Cover B st) :
    cands f I B st.S ⊆ cands f I st.rem st.S := by
  classical
  intro u hu
  obtain ⟨huB, huS, huI, hupos⟩ := Finset.mem_filter.mp hu
  have hur : u ∈ st.rem := (Finset.mem_union.mp (hc huB)).resolve_right huS
  exact Finset.mem_filter.mpr ⟨hur, huS, huI, hupos⟩

theorem finish_alg2_step {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (hc : Cover B st) :
    finish f I B (alg2Step f I B st).S = finish f I B st.S := by
  classical
  cases hp : pick f I st.rem st.S with
  | none => simp only [alg2Step, hp]
  | some u =>
    by_cases hu : u ∈ B
    · have hB := pick_restrict f I B st.rem st.S u (cover_cands f I B st hc) hu hp
      simpa only [alg2Step, hp, if_pos hu, greedyStep, hB] using finish_step f I B st.S
    · simp only [alg2Step, hp, if_neg hu]

theorem simulation {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) (j : ℕ) :
    let st := (alg2Step f I B)^[j] (alg2Init T)
    Cover B st ∧ finish f I B st.S = sampleGreedy f I B := by
  induction j with
  | zero =>
    constructor
    · intro u hu
      simp [alg2Init]
    · rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    dsimp only at ih ⊢
    exact ⟨cover_step f I B _ ih.1, (finish_alg2_step f I B _ ih.1).trans ih.2⟩

theorem fixed_coins {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) : sampleGreedy f I B = (alg2 f I T B).S := by
  have hsim := simulation f I T B (Fintype.card α)
  change Cover B (alg2 f I T B) ∧
    finish f I B (alg2 f I T B).S = sampleGreedy f I B at hsim
  have hsub := cover_cands f I B (alg2 f I T B) hsim.1
  have hempty := cands_empty_of_pick_none f I _ _ (terminated f I T B)
  have hBempty : cands f I B (alg2 f I T B).S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have := hsub hu
    rw [hempty] at this
    exact Finset.notMem_empty u this
  exact hsim.2.symm.trans (finish_of_none f I B _ (pick_none_of_cands_empty f I _ _ hBempty))

end SubsampleSubmod.SampleGreedy.EquivalenceProof

open SubsampleSubmod.SampleGreedy

theorem solution {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (q : ℝ) (T R : Finset α) :
    ∑ N' : Finset α, sampleWeight q N' * (if sampleGreedy f I N' = R then (1 : ℝ) else 0) =
      ∑ B : Finset α, sampleWeight q B * (if (alg2 f I T B).S = R then (1 : ℝ) else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro B hB
  rw [EquivalenceProof.fixed_coins f I T B]
