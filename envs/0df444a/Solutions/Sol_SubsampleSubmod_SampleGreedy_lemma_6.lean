-- Prove2me | solution 1 for SubsampleSubmod.SampleGreedy.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:29:30.162034+00:00
-- url     : https://prove2.me/submissions/40fc53ab-2176-4779-8d7a-973104937628

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis
import Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_5

namespace SubsampleSubmod.SampleGreedy.Pathwise

open Finset

/- Complete helper proofs reused from our accepted Lemma 5 submission. Platform imports expose only the registered lemma, so these helpers are checked locally in the submitted file. -/
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

/-- A feasible protected subset supplies a witness for the repair operation. -/
theorem local_minRemoval_spec {α : Type} [DecidableEq α]
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


theorem diminishing {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (A C : Finset α)
    (hAC : A ⊆ C) (v : α) (hv : v ∉ C) : marg f v C ≤ marg f v A := by
  have h := hf (insert v A) C
  rw [Finset.insert_union, Finset.union_eq_right.mpr hAC,
    Finset.insert_inter_of_notMem hv, Finset.inter_eq_left.mpr hAC] at h
  unfold marg
  linarith

theorem union_bound {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (A D : Finset α) :
    f (A ∪ D) ≤ f A + ∑ v ∈ D, marg f v A := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert v D hvD ih =>
    by_cases hvA : v ∈ A
    · simpa [Finset.sum_insert hvD, Finset.union_insert, Finset.insert_eq_of_mem hvA,
        Finset.insert_eq_of_mem (Finset.mem_union_left D hvA), marg] using ih
    · have hvAD : v ∉ A ∪ D := by simp [hvA, hvD]
      have hm := diminishing f hf A (A ∪ D) Finset.subset_union_left v hvAD
      rw [Finset.union_insert, Finset.sum_insert hvD]
      change f (insert v (A ∪ D)) - f (A ∪ D) ≤ marg f v A at hm
      linarith

theorem removal_bound {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (F O X : Finset α) (m : ℝ)
    (hXO : X ⊆ O) (hm : ∀ v ∈ X \ F, marg f v F ≤ m) :
    f (F ∪ O) ≤ f (F ∪ (O \ X)) + ((X \ F).card : ℝ) * m := by
  classical
  have heq : (F ∪ (O \ X)) ∪ (X \ F) = F ∪ O := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr h.1
      · exact Or.inr (hXO h.1)
    · intro h
      by_cases hvF : v ∈ F
      · exact Or.inl (Or.inl hvF)
      · have hvO := h.resolve_left hvF
        by_cases hvX : v ∈ X
        · exact Or.inr ⟨hvX, hvF⟩
        · exact Or.inl (Or.inr ⟨hvO, hvX⟩)
  have hb := union_bound f hf (F ∪ (O \ X)) (X \ F)
  rw [heq] at hb
  have hs : (∑ v ∈ X \ F, marg f v (F ∪ (O \ X))) ≤ ((X \ F).card : ℝ) * m := by
    calc
      _ ≤ ∑ v ∈ X \ F, m := by
        apply Finset.sum_le_sum
        intro v hv
        have hvX := (Finset.mem_sdiff.mp hv).1
        have hvF := (Finset.mem_sdiff.mp hv).2
        have hvA : v ∉ F ∪ (O \ X) := by simp [hvF, hvX]
        exact (diminishing f hf F (F ∪ (O \ X)) Finset.subset_union_left v hvA).trans (hm v hv)
      _ = _ := by simp
  linarith

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
    | none => exact Or.inl (by simpa only [alg2Step, hp] using hp)
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

noncomputable def cost {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (F : Finset α) (Ou Su : α → Finset α) : ℝ :=
  ∑ u : α, ((Ou u \ F).card : ℝ) * marg f u (Su u)

theorem cost_update {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (F : Finset α) (Ou Su : α → Finset α)
    (u : α) (X S : Finset α) (hu : Ou u = ∅) :
    cost f F (Function.update Ou u X) (Function.update Su u S) =
      cost f F Ou Su + ((X \ F).card : ℝ) * marg f u S := by
  classical
  have heq : (fun v => (((Function.update Ou u X) v \ F).card : ℝ) *
      marg f v ((Function.update Su u S) v)) =
      (fun v => ((Ou v \ F).card : ℝ) * marg f v (Su v) +
        if v = u then ((X \ F).card : ℝ) * marg f u S else 0) := by
    funext v
    by_cases hv : v = u
    · subst v
      simp [hu]
    · simp [Function.update_of_ne hv, hv]
  unfold cost
  rw [heq, Finset.sum_add_distrib]
  simp

theorem potential_step {α : Type} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (T B : Finset α) (st : Alg2State α)
    (hO : I st.O) (hSO : st.S ⊆ st.O)
    (hUnconsidered : ∀ v ∈ st.O \ st.S, v ∉ st.considered)
    (hFresh : Fresh st)
    (hpot : ∀ F : Finset α, st.S ⊆ F →
      f (F ∪ T) ≤ f (F ∪ st.O) + cost f F st.Ou st.Su)
    (F : Finset α) (hnew : (alg2Step f I B st).S ⊆ F) :
    f (F ∪ T) ≤ f (F ∪ (alg2Step f I B st).O) +
      cost f F (alg2Step f I B st).Ou (alg2Step f I B st).Su := by
  classical
  have hSF := (step_S_mono f I B st).trans hnew
  have hprev := hpot F hSF
  cases hp : pick f I st.rem st.S with
  | none => simpa only [alg2Step, hp] using hprev
  | some u =>
    obtain ⟨hurem, huS, hIS⟩ := local_pick_spec f I st.rem st.S u hp
    have hOldOu : st.Ou u = ∅ := hFresh.2 u hurem
    by_cases huB : u ∈ B
    · let X := minRemoval I (insert u st.O) (insert u st.S)
      have hX : X ⊆ insert u st.O \ insert u st.S :=
        (local_minRemoval_spec I (insert u st.O) (insert u st.S)
          (Finset.insert_subset_insert u hSO) hIS).1
      have hnew' : insert u st.S ⊆ F := by
        simpa only [alg2Step, hp, if_pos huB] using hnew
      have huF : u ∈ F := hnew' (Finset.mem_insert_self _ _)
      have hm : ∀ v ∈ X \ F, marg f v F ≤ marg f u st.S := by
        intro v hv
        have hvX := hX (Finset.mem_sdiff.mp hv).1
        have hvF := (Finset.mem_sdiff.mp hv).2
        have hvIns := (Finset.mem_sdiff.mp hvX).1
        have hvNotIns := (Finset.mem_sdiff.mp hvX).2
        have hvne : v ≠ u := by
          intro heq
          exact hvNotIns (heq ▸ Finset.mem_insert_self _ _)
        have hvO : v ∈ st.O := (Finset.mem_insert.mp hvIns).resolve_left hvne
        have hvS : v ∉ st.S := fun hvS => hvNotIns (Finset.mem_insert_of_mem hvS)
        have hvRem : v ∈ st.rem := (hFresh.1 v).mpr
          (hUnconsidered v (Finset.mem_sdiff.mpr ⟨hvO, hvS⟩))
        have hvI : I (insert v st.S) := hI.2 _ _ (Finset.insert_subset hvO hSO) hO
        exact (diminishing f hsub st.S F hSF v hvF).trans
          (pick_max f I st.rem st.S u hp v hvRem hvS hvI)
      have hr := removal_bound f hsub F (insert u st.O) X (marg f u st.S)
        (hX.trans Finset.sdiff_subset) hm
      rw [Finset.union_insert, Finset.insert_eq_of_mem (Finset.mem_union_left st.O huF)] at hr
      simp only [alg2Step, hp, if_pos huB]
      change f (F ∪ T) ≤ f (F ∪ (insert u st.O \ X)) +
        cost f F (Function.update st.Ou u X) (Function.update st.Su u st.S)
      rw [cost_update f F st.Ou st.Su u X st.S hOldOu]
      linarith
    · let X : Finset α := if u ∈ st.O then {u} else ∅
      have hXO : X ⊆ st.O := by
        dsimp only [X]
        split <;> simp_all
      have hXu : X ⊆ {u} := by dsimp only [X]; split <;> simp
      have hm : ∀ v ∈ X \ F, marg f v F ≤ marg f u st.S := by
        intro v hv
        have hvu : v = u := Finset.mem_singleton.mp (hXu (Finset.mem_sdiff.mp hv).1)
        subst v
        exact diminishing f hsub st.S F hSF u (Finset.mem_sdiff.mp hv).2
      have hr := removal_bound f hsub F st.O X (marg f u st.S) hXO hm
      simp only [alg2Step, hp, if_neg huB]
      change f (F ∪ T) ≤ f (F ∪ (st.O \ X)) +
        cost f F (Function.update st.Ou u X) (Function.update st.Su u st.S)
      rw [cost_update f F st.Ou st.Su u X st.S hOldOu]
      linarith

theorem potential_run {α : Type} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (T : Finset α) (hT : I T) (B : Finset α) (j : ℕ) :
    let st := (alg2Step f I B)^[j] (alg2Init T)
    ∀ F : Finset α, st.S ⊆ F →
      f (F ∪ T) ≤ f (F ∪ st.O) + cost f F st.Ou st.Su := by
  induction j with
  | zero => simp [alg2Init, cost]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hO, hSO, hUC⟩ := lemma_5 f I hI T hT B j
    exact potential_step f I hsub hI T B _ hO hSO hUC
      (fresh_run f I T B j) ih

theorem final_union_bound {α : Type} [Fintype α] [LinearOrder α]
    (f : Finset α → ℝ) (I : Finset α → Prop)
    (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (T : Finset α) (hT : I T) (B : Finset α) :
    f ((alg2 f I T B).S ∪ (alg2 f I T B).O) ≤ f (alg2 f I T B).S := by
  let st := alg2 f I T B
  change f (st.S ∪ st.O) ≤ f st.S
  obtain ⟨hO, hSO, hUC⟩ := lemma_5 f I hI T hT B (Fintype.card α)
  change I st.O at hO
  change st.S ⊆ st.O at hSO
  change ∀ v ∈ st.O \ st.S, v ∉ st.considered at hUC
  have hFresh : Fresh st := fresh_run f I T B (Fintype.card α)
  have hp : pick f I st.rem st.S = none := terminated f I T B
  have hm : ∀ v ∈ st.O, marg f v st.S ≤ 0 := by
    intro v hvO
    by_cases hvS : v ∈ st.S
    · simp [marg, Finset.insert_eq_of_mem hvS]
    · have hvRem : v ∈ st.rem := (hFresh.1 v).mpr
        (hUC v (Finset.mem_sdiff.mpr ⟨hvO, hvS⟩))
      have hvI : I (insert v st.S) := hI.2 _ _ (Finset.insert_subset hvO hSO) hO
      exact pick_none_nonpos f I st.rem st.S hp v hvRem hvS hvI
  have hs : (∑ v ∈ st.O, marg f v st.S) ≤ 0 := Finset.sum_nonpos hm
  have hb := union_bound f hsub st.S st.O
  linarith

end SubsampleSubmod.SampleGreedy.Pathwise

open SubsampleSubmod.SampleGreedy

theorem solution {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (hsub : NonmonotoneSubmod.Shared.Submodular f) (hI : IsIndepSystem I)
    (T : Finset α) (hT : I T) (B : Finset α) :
    f ((alg2 f I T B).S ∪ T) -
        ∑ u : α, (((alg2 f I T B).Ou u \ (alg2 f I T B).S).card : ℝ) *
          marg f u ((alg2 f I T B).Su u) ≤
      f (alg2 f I T B).S := by
  have hp := Pathwise.potential_run f I hsub hI T hT B (Fintype.card α)
    (alg2 f I T B).S (Finset.Subset.refl _)
  have hf := Pathwise.final_union_bound f I hsub hI T hT B
  change f ((alg2 f I T B).S ∪ T) ≤
    f ((alg2 f I T B).S ∪ (alg2 f I T B).O) +
      (∑ u : α, (((alg2 f I T B).Ou u \ (alg2 f I T B).S).card : ℝ) *
        marg f u ((alg2 f I T B).Su u)) at hp
  linarith
