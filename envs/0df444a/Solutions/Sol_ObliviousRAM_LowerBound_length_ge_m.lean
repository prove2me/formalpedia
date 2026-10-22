-- Prove2me | solution 1 for ObliviousRAM.LowerBound.length_ge_m
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:25:54.89307+00:00
-- url     : https://prove2.me/submissions/f4f4bcc2-ca17-44bc-8c23-062df626fb0d

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

set_option autoImplicit false
open ObliviousRAM.LowerBound

/-- Invariant: every ball is either still in its home cell or its home cell was visited. -/
def CCInv {m : ℕ} (s : State m) (V : Set (Fin m)) : Prop :=
  (∀ v β, s.cell v = some β → v = β ∨ β ∈ V) ∧ (∀ β ∈ s.hand, β ∈ V)

lemma CCInv_mono {m : ℕ} {s : State m} {V W : Set (Fin m)} (h : CCInv s V) (hVW : V ⊆ W) :
    CCInv s W :=
  ⟨fun v β hc => (h.1 v β hc).imp_right (fun hb => hVW hb), fun β hb => hVW (h.2 β hb)⟩

lemma CCInv_init (m : ℕ) : CCInv (initState m) ∅ := by
  refine ⟨?_, ?_⟩
  · intro v β hc
    left
    simp [initState] at hc
    exact hc
  · intro β hb
    simp [initState] at hb

lemma CCInv_step {m : ℕ} (b : ℕ) (s s' : State m) (act : Action m) (V : Set (Fin m))
    (h : CCInv s V) (hs : step b s act = some s') : CCInv s' (insert act.1 V) := by
  obtain ⟨v, op⟩ := act
  cases op with
  | take =>
    simp only [step] at hs
    cases hc : s.cell v with
    | none => simp [hc] at hs
    | some β' =>
      simp only [hc] at hs
      split_ifs at hs with hcard
      · cases hs
        refine ⟨?_, ?_⟩
        · intro w β hw
          by_cases hwv : w = v
          · subst hwv
            simp at hw
          · simp only [Function.update_apply, hwv, if_false] at hw
            rcases h.1 w β hw with h1 | h1
            · exact Or.inl h1
            · exact Or.inr (Set.mem_insert_of_mem _ h1)
        · intro β hβ
          simp only [Finset.mem_insert] at hβ
          rcases hβ with rfl | hβ
          · rcases h.1 v β hc with h1 | h1
            · subst h1; exact Set.mem_insert _ _
            · exact Set.mem_insert_of_mem _ h1
          · exact Set.mem_insert_of_mem _ (h.2 β hβ)
  | place β =>
    simp only [step] at hs
    split_ifs at hs with hcond
    · cases hs
      refine ⟨?_, ?_⟩
      · intro w γ hw
        by_cases hwv : w = v
        · subst hwv
          simp at hw
          subst hw
          right
          exact Set.mem_insert_of_mem _ (h.2 _ hcond.2)
        · simp only [Function.update_apply, hwv, if_false] at hw
          rcases h.1 w γ hw with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Set.mem_insert_of_mem _ h1)
      · intro γ hγ
        exact Set.mem_insert_of_mem _ (h.2 γ (Finset.mem_of_mem_erase hγ))
  | nothing =>
    simp only [step] at hs
    cases hs
    exact CCInv_mono h (Set.subset_insert _ _)

lemma CCfold_none {m : ℕ} (b : ℕ) (l : List (Action m)) :
    l.foldl (fun os act => os.bind (fun s => step b s act)) none = none := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa using ih

lemma CCInv_fold {m : ℕ} (b : ℕ) (l : List (Action m)) :
    ∀ (s0 s : State m) (V : Set (Fin m)), CCInv s0 V →
      l.foldl (fun os act => os.bind (fun s => step b s act)) (some s0) = some s →
      CCInv s (V ∪ {v | v ∈ visible l}) := by
  induction l with
  | nil =>
    intro s0 s V h hf
    simp at hf
    subst hf
    exact CCInv_mono h (by intro x hx; exact Or.inl hx)
  | cons act l ih =>
    intro s0 s V h hf
    simp only [List.foldl_cons, Option.bind_some] at hf
    cases hst : step b s0 act with
    | none =>
      rw [hst] at hf
      rw [CCfold_none] at hf
      cases hf
    | some s1 =>
      rw [hst] at hf
      have h1 := CCInv_step b s0 s1 act V h hst
      have h2 := ih s1 s _ h1 hf
      refine CCInv_mono h2 ?_
      intro x hx
      rcases hx with (rfl | hx) | hx
      · exact Or.inr (by simp [visible])
      · exact Or.inl hx
      · exact Or.inr (by simp [visible] at hx ⊢; exact Or.inr hx)

lemma CChand_mem_visible {m : ℕ} (b : ℕ) (a : List (Action m)) (j : ℕ) (β : Fin m)
    (hβ : β ∈ handAfter b a j) : β ∈ visible a := by
  unfold handAfter at hβ
  cases hs : stateAfter b a j with
  | none => simp [hs] at hβ
  | some s =>
    simp only [hs, Option.map_some, Option.getD_some] at hβ
    have hinv := CCInv_fold b (a.take j) (initState m) s ∅ (CCInv_init m) hs
    have := hinv.2 β hβ
    rcases this with h | h
    · exact absurd h (by simp)
    · simp only [visible, List.mem_map] at h ⊢
      obtain ⟨x, hx, hxe⟩ := h
      exact ⟨x, List.mem_of_mem_take hx, hxe⟩

theorem solution {b m t : ℕ} (ht : 1 ≤ t) (P : ObliviousPlayer b m t)
    (r : Fin t → Fin m) (a : List (Action m)) (ha : a ∈ (P.play r).support) :
    m ≤ a.length := by
  have key : ∀ β : Fin m, β ∈ visible a := by
    intro β
    have h1 : visible a ∈ ((P.play r).map visible).support :=
      (PMF.mem_support_map_iff _ _ _).2 ⟨a, ha, rfl⟩
    rw [P.oblivious r (fun _ => β)] at h1
    obtain ⟨a', ha', hv⟩ := (PMF.mem_support_map_iff _ _ _).1 h1
    obtain ⟨_, j, _, _, _, _, hmem⟩ := P.correct (fun _ => β) a' ha'
    have := CChand_mem_visible b a' _ β (hmem ⟨0, ht⟩)
    rw [← hv]; exact this
  have hsub : (Finset.univ : Finset (Fin m)) ⊆ (visible a).toFinset :=
    fun β _ => by simpa using key β
  calc m = (Finset.univ : Finset (Fin m)).card := by simp
    _ ≤ (visible a).toFinset.card := Finset.card_le_card hsub
    _ ≤ (visible a).length := List.toFinset_card_le _
    _ = a.length := by simp [visible]
