-- Prove2me | solution 1 for SubsampleSubmod.SampleGreedy.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:48:29.025179+00:00
-- url     : https://prove2.me/submissions/eba95f37-4609-4eb5-b8f0-5b66c642951e

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy.LinearRemoval

open Finset

/- Complete membership, repair, invariant, freshness and termination helper proofs
are reused from the checked greedy-invariants and greedy-pathwise submissions.
The proof bodies are included locally; no platform theorem helpers are imported. -/

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

theorem invariant_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
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

theorem pick_details {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (u : α)
    (hp : pick f I pool S = some u) :
    u ∈ cands f I pool S ∧ ∀ v ∈ cands f I pool S, marg f v S ≤ marg f u S := by
  classical
  unfold pick at hp
  dsimp only at hp
  split at hp
  · rename_i hn
    have hmem := Finset.min'_mem _ hn
    rw [Option.some.inj hp] at hmem
    exact Finset.mem_filter.mp hmem
  · cases hp

theorem pick_max {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α) (u : α)
    (hp : pick f I pool S = some u) (v : α)
    (hvpool : v ∈ pool) (hvS : v ∉ S) (hvI : I (insert v S)) :
    marg f v S ≤ marg f u S := by
  classical
  obtain ⟨hu, hmax⟩ := pick_details f I pool S u hp
  have huPos : 0 < marg f u S := (Finset.mem_filter.mp hu).2.2.2
  by_cases hvPos : 0 < marg f v S
  · exact hmax v (by simp [cands, hvpool, hvS, hvI, hvPos])
  · exact (le_of_not_gt hvPos).trans huPos.le

theorem pick_none_nonpos {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (pool S : Finset α)
    (hp : pick f I pool S = none) (v : α)
    (hvpool : v ∈ pool) (hvS : v ∉ S) (hvI : I (insert v S)) : marg f v S ≤ 0 := by
  classical
  by_contra hn
  have hvPos : 0 < marg f v S := lt_of_not_ge hn
  have hvC : v ∈ cands f I pool S := by simp [cands, hvpool, hvS, hvI, hvPos]
  have hC : (cands f I pool S).Nonempty := ⟨v, hvC⟩
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image (cands f I pool S) (fun u => marg f u S) hC
  have hM : ((cands f I pool S).filter
      (fun u => ∀ v ∈ cands f I pool S, marg f v S ≤ marg f u S)).Nonempty :=
    ⟨u, Finset.mem_filter.mpr ⟨hu, hmax⟩⟩
  unfold pick at hp
  dsimp only at hp
  rw [dif_pos hM] at hp
  cases hp

def Fresh {α : Type} (st : Alg2State α) : Prop :=
  (∀ v, v ∈ st.rem ↔ v ∉ st.considered) ∧ ∀ v ∈ st.rem, st.Ou v = ∅

theorem fresh_step {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α) (h : Fresh st) :
    Fresh (alg2Step f I B st) := by
  classical
  cases hp : pick f I st.rem st.S with
  | none => simpa only [alg2Step, hp] using h
  | some u =>
    have hrem : ∀ v, v ∈ st.rem.erase u ↔ v ∉ insert u st.considered := by
      intro v
      simp only [Finset.mem_erase, Finset.mem_insert, not_or, h.1]
    have hupdate : ∀ (X : Finset α) v, v ∈ st.rem.erase u →
        Function.update st.Ou u X v = ∅ := by
      intro X v hv
      rw [Function.update_of_ne (Finset.mem_erase.mp hv).1]
      exact h.2 v (Finset.mem_erase.mp hv).2
    unfold Fresh
    simp only [alg2Step, hp]
    split <;> exact ⟨hrem, hupdate _⟩

theorem fresh_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) (j : ℕ) :
    Fresh ((alg2Step f I B)^[j] (alg2Init T)) := by
  induction j with
  | zero => simp [Fresh, alg2Init]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact fresh_step f I B _ ih

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
      have hu := (greedyInvariant_pick_spec f I st.rem st.S u hp).1
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
      have hu := (greedyInvariant_pick_spec f I _ _ u hp).1
      have hpos : 0 < (alg2 f I T B).rem.card := Finset.card_pos.mpr ⟨u, hu⟩
      omega


theorem linear_marg {α : Type} [DecidableEq α] (f : Finset α → ℝ)
    (hlin : IsLinear f) (hf_empty : f ∅ = 0) (u : α) (S : Finset α) (hu : u ∉ S) :
    marg f u S = f {u} := by
  have h := hlin ∅ S u (Finset.empty_subset _) hu
  simpa [hf_empty, marg] using h.symm

theorem linear_insert {α : Type} [DecidableEq α] (f : Finset α → ℝ)
    (hlin : IsLinear f) (hf_empty : f ∅ = 0) (u : α) (S : Finset α) (hu : u ∉ S) :
    f (insert u S) = f S + f {u} := by
  have h := linear_marg f hlin hf_empty u S hu
  unfold marg at h
  linarith

theorem linear_sum {α : Type} [DecidableEq α] (f : Finset α → ℝ)
    (hlin : IsLinear f) (hf_empty : f ∅ = 0) (S : Finset α) :
    f S = ∑ u ∈ S, f {u} := by
  induction S using Finset.induction_on with
  | empty => simpa using hf_empty
  | @insert u S hu ih => rw [linear_insert f hlin hf_empty u S hu, ih, Finset.sum_insert hu]; ring

theorem linear_remove {α : Type} [DecidableEq α] (f : Finset α → ℝ)
    (hlin : IsLinear f) (hf_empty : f ∅ = 0) (O X : Finset α) (hXO : X ⊆ O) :
    f O = f (O \ X) + f X := by
  rw [linear_sum f hlin hf_empty O, linear_sum f hlin hf_empty (O \ X), linear_sum f hlin hf_empty X]
  exact (Finset.sum_sdiff hXO).symm

theorem linear_removal_bound {α : Type} [DecidableEq α] (f : Finset α → ℝ)
    (hlin : IsLinear f) (hf_empty : f ∅ = 0) (O X : Finset α) (hXO : X ⊆ O)
    (c : ℝ) (hc : ∀ u ∈ X, f {u} ≤ c) :
    f O ≤ f (O \ X) + (X.card : ℝ) * c := by
  rw [linear_remove f hlin hf_empty O X hXO]
  apply add_le_add le_rfl
  rw [linear_sum f hlin hf_empty]
  calc
    _ ≤ ∑ _u ∈ X, c := Finset.sum_le_sum hc
    _ = _ := by simp

theorem fresh_y_step {α : Type} [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (B : Finset α) (st : Alg2State α)
    (h : ∀ v ∈ st.rem, v ∉ st.Y) :
    ∀ v ∈ (alg2Step f I B st).rem, v ∉ (alg2Step f I B st).Y := by
  classical
  cases hp : pick f I st.rem st.S with
  | none => simpa only [alg2Step, hp] using h
  | some u =>
    have hold : ∀ v ∈ st.rem.erase u, v ∉ st.Y :=
      fun v hv => h v (Finset.mem_erase.mp hv).2
    have hnew : ∀ v ∈ st.rem.erase u, v ∉ insert u st.Y := by
      intro v hv
      simp only [Finset.mem_insert, not_or]
      exact ⟨(Finset.mem_erase.mp hv).1, hold v hv⟩
    simp only [alg2Step, hp]
    split
    · split <;> assumption
    · exact hold

theorem fresh_y_run {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (T B : Finset α) (j : ℕ) :
    let st := (alg2Step f I B)^[j] (alg2Init T)
    ∀ v ∈ st.rem, v ∉ st.Y := by
  induction j with
  | zero => simp [alg2Init]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact fresh_y_step f I B _ ih

noncomputable def charge {α : Type} [Fintype α]
    (f : Finset α → ℝ) (Ou : α → Finset α) (Y : Finset α) : ℝ :=
  (∑ u : α, ((Ou u).card : ℝ) * f {u}) - ∑ u ∈ Y, f {u}

theorem charge_update {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (Ou : α → Finset α) (Y : Finset α)
    (u : α) (X : Finset α) (hu : Ou u = ∅) :
    charge f (Function.update Ou u X) Y = charge f Ou Y + (X.card : ℝ) * f {u} := by
  classical
  have heq : (fun v => (((Function.update Ou u X) v).card : ℝ) * f {v}) =
      (fun v => ((Ou v).card : ℝ) * f {v} + if v = u then (X.card : ℝ) * f {u} else 0) := by
    funext v
    by_cases hv : v = u
    · subst v; simp [hu]
    · simp [hv]
  unfold charge
  rw [heq, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem charge_insert_y {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (Ou : α → Finset α) (Y : Finset α)
    (u : α) (hu : u ∉ Y) : charge f Ou (insert u Y) = charge f Ou Y - f {u} := by
  unfold charge
  rw [Finset.sum_insert hu]
  ring

theorem charge_eq {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (Ou : α → Finset α) (Y : Finset α) :
    charge f Ou Y = ∑ u : α, (((Ou u).card : ℝ) - (if u ∈ Y then (1 : ℝ) else 0)) * f {u} := by
  classical
  simp [charge, sub_mul, Finset.sum_sub_distrib]

theorem potential_step {α : Type} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (hlin : IsLinear f)
    (hf_empty : f ∅ = 0) (hI : IsIndepSystem I) (B : Finset α) (st : Alg2State α)
    (hO : I st.O) (hSO : st.S ⊆ st.O)
    (hUC : ∀ v ∈ st.O \ st.S, v ∉ st.considered)
    (hFresh : Fresh st) (hY : ∀ v ∈ st.rem, v ∉ st.Y) :
    f st.O + charge f st.Ou st.Y ≤
      f (alg2Step f I B st).O + charge f (alg2Step f I B st).Ou (alg2Step f I B st).Y := by
  classical
  cases hp : pick f I st.rem st.S with
  | none => simp only [alg2Step, hp, le_refl]
  | some u =>
    obtain ⟨hurem, huS, hIS⟩ := greedyInvariant_pick_spec f I st.rem st.S u hp
    have hOu : st.Ou u = ∅ := hFresh.2 u hurem
    have huY : u ∉ st.Y := hY u hurem
    by_cases huB : u ∈ B
    · let X := minRemoval I (insert u st.O) (insert u st.S)
      have hX : X ⊆ insert u st.O \ insert u st.S :=
        (greedyInvariant_minRemoval_spec I (insert u st.O) (insert u st.S)
          (Finset.insert_subset_insert u hSO) hIS).1
      have hm : ∀ v ∈ X, f {v} ≤ f {u} := by
        intro v hv
        obtain ⟨hvIns, hvNotIns⟩ := Finset.mem_sdiff.mp (hX hv)
        have hvne : v ≠ u := by
          intro heq
          exact hvNotIns (heq ▸ Finset.mem_insert_self _ _)
        have hvO : v ∈ st.O := (Finset.mem_insert.mp hvIns).resolve_left hvne
        have hvS : v ∉ st.S := fun hv => hvNotIns (Finset.mem_insert_of_mem hv)
        have hvRem : v ∈ st.rem := (hFresh.1 v).mpr (hUC v (Finset.mem_sdiff.mpr ⟨hvO, hvS⟩))
        have hvI : I (insert v st.S) := hI.2 _ _ (Finset.insert_subset hvO hSO) hO
        have hb := pick_max f I st.rem st.S u hp v hvRem hvS hvI
        rwa [linear_marg f hlin hf_empty v st.S hvS,
          linear_marg f hlin hf_empty u st.S huS] at hb
      have hb := linear_removal_bound f hlin hf_empty (insert u st.O) X
        (hX.trans Finset.sdiff_subset) (f {u}) hm
      by_cases huO : u ∈ st.O
      · rw [Finset.insert_eq_of_mem huO] at hb
        simp only [alg2Step, hp, if_pos huB, if_pos huO]
        change f st.O + charge f st.Ou st.Y ≤
          f (insert u st.O \ X) + charge f (Function.update st.Ou u X) st.Y
        rw [charge_update f st.Ou st.Y u X hOu, Finset.insert_eq_of_mem huO]
        linarith
      · rw [linear_insert f hlin hf_empty u st.O huO] at hb
        simp only [alg2Step, hp, if_pos huB, if_neg huO]
        change f st.O + charge f st.Ou st.Y ≤
          f (insert u st.O \ X) + charge f (Function.update st.Ou u X) (insert u st.Y)
        rw [charge_update f st.Ou (insert u st.Y) u X hOu, charge_insert_y f st.Ou st.Y u huY]
        linarith
    · let X : Finset α := if u ∈ st.O then {u} else ∅
      have hXO : X ⊆ st.O := by dsimp only [X]; split <;> simp_all
      have hXu : X ⊆ {u} := by dsimp only [X]; split <;> simp
      have hm : ∀ v ∈ X, f {v} ≤ f {u} := by
        intro v hv
        rw [Finset.mem_singleton.mp (hXu hv)]
      have hb := linear_removal_bound f hlin hf_empty st.O X hXO (f {u}) hm
      simp only [alg2Step, hp, if_neg huB]
      change f st.O + charge f st.Ou st.Y ≤
        f (st.O \ X) + charge f (Function.update st.Ou u X) st.Y
      rw [charge_update f st.Ou st.Y u X hOu]
      linarith

theorem potential_run {α : Type} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (hlin : IsLinear f)
    (hf_empty : f ∅ = 0) (hI : IsIndepSystem I)
    (T : Finset α) (hT : I T) (B : Finset α) (j : ℕ) :
    let st := (alg2Step f I B)^[j] (alg2Init T)
    f T ≤ f st.O + charge f st.Ou st.Y := by
  induction j with
  | zero => simp [alg2Init, charge]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hO, hSO, hUC⟩ := invariant_run f I hI T hT B j
    exact ih.trans (potential_step f I hlin hf_empty hI B _ hO hSO hUC
      (fresh_run f I T B j) (fresh_y_run f I T B j))

theorem final_comparison {α : Type} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop) (hlin : IsLinear f)
    (hf_empty : f ∅ = 0) (hI : IsIndepSystem I)
    (T : Finset α) (hT : I T) (B : Finset α) : f (alg2 f I T B).O ≤ f (alg2 f I T B).S := by
  let st := alg2 f I T B
  change f st.O ≤ f st.S
  obtain ⟨hO, hSO, hUC⟩ := invariant_run f I hI T hT B (Fintype.card α)
  change I st.O at hO
  change st.S ⊆ st.O at hSO
  change ∀ v ∈ st.O \ st.S, v ∉ st.considered at hUC
  have hFresh : Fresh st := fresh_run f I T B (Fintype.card α)
  have hp : pick f I st.rem st.S = none := terminated f I T B
  have htail : f (st.O \ st.S) ≤ 0 := by
    rw [linear_sum f hlin hf_empty]
    apply Finset.sum_nonpos
    intro v hv
    obtain ⟨hvO, hvS⟩ := Finset.mem_sdiff.mp hv
    have hvRem : v ∈ st.rem := (hFresh.1 v).mpr (hUC v hv)
    have hvI : I (insert v st.S) := hI.2 _ _ (Finset.insert_subset hvO hSO) hO
    have hb := pick_none_nonpos f I st.rem st.S hp v hvRem hvS hvI
    rwa [linear_marg f hlin hf_empty v st.S hvS] at hb
  rw [linear_remove f hlin hf_empty st.O st.S hSO]
  linarith

end SubsampleSubmod.SampleGreedy.LinearRemoval

open SubsampleSubmod.SampleGreedy

theorem solution {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hlin : IsLinear f) (hf_empty : f ∅ = 0) (hI : IsIndepSystem I)
    (T : Finset α) (hT : I T) (B : Finset α) :
    f T - ∑ u : α, ((((alg2 f I T B).Ou u).card : ℝ) - (if u ∈ (alg2 f I T B).Y then (1 : ℝ) else 0)) *
        f {u} ≤
      f (alg2 f I T B).S := by
  have hp := LinearRemoval.potential_run f I hlin hf_empty hI T hT B (Fintype.card α)
  have hf := LinearRemoval.final_comparison f I hlin hf_empty hI T hT B
  change f T ≤ f (alg2 f I T B).O + LinearRemoval.charge f (alg2 f I T B).Ou (alg2 f I T B).Y at hp
  rw [LinearRemoval.charge_eq] at hp
  linarith
