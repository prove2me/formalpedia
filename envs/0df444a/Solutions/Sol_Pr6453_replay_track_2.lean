-- Prove2me | solution 2 for Pr6453.replay_track
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T22:09:15.140174+00:00
-- url     : https://prove2.me/submissions/741df679-6c71-4126-96dc-8527064b5f94

/-
PR #6453: the frame a column ends at is what its own track computes.
-/
import Definitions.Def_Pr6453_Locality
import Definitions.Def_Pr6453_Track

set_option autoImplicit false

namespace Pr6453

theorem frameStep?_other {n : ℕ} (e : Event n) (fr : Fin n → Option ℕ) (c : Fin n)
    (h : ¬ Writes e c) (g : Fin n → Option ℕ) (hg : frameStep? e fr = some g) : g c = fr c := by
  cases e with
  | MOVE c' s t =>
      simp only [Writes] at h
      by_cases hc : fr c' = some s
      · have hne : c' ≠ c := fun he => h he
        simp only [frameStep?, hc, if_true, Option.some.injEq] at hg
        subst hg
        exact Function.update_of_ne (Ne.symm hne) _ _
      · simp [frameStep?, hc] at hg
  | INIT c' f =>
      simp only [Writes] at h
      by_cases hc : fr c' = none
      · have hne : c' ≠ c := fun he => h he
        simp only [frameStep?, hc, if_true, Option.some.injEq] at hg
        subst hg
        exact Function.update_of_ne (Ne.symm hne) _ _
      · simp [frameStep?, hc] at hg
  | CLEAR c' f =>
      simp only [Writes] at h
      by_cases hc : fr c' = some f
      · have hne : c' ≠ c := fun he => h he
        simp only [frameStep?, hc, if_true, Option.some.injEq] at hg
        subst hg
        exact Function.update_of_ne (Ne.symm hne) _ _
      · simp [frameStep?, hc] at hg
  | SCALE c' f q =>
      by_cases hc : fr c' = some f <;> simp [frameStep?, hc] at hg ⊢
      exact hg ▸ rfl
  | ADD d s q f =>
      by_cases hc : fr d = some f ∧ fr s = some f <;> simp [frameStep?, hc] at hg ⊢
      exact hg ▸ rfl

theorem frameStep?_move {n : ℕ} (c' : Fin n) (s t : ℕ) (fr : Fin n → Option ℕ)
    (fr' : Fin n → Option ℕ) (hs : frameStep? (Event.MOVE c' s t) fr = some fr') :
    fr c' = some s ∧ fr' = Function.update fr c' (some t) := by
  simp only [frameStep?] at hs
  by_cases hg : fr c' = some s
  · rw [if_pos hg] at hs
    exact ⟨hg, (Option.some.inj hs).symm⟩
  · rw [if_neg hg] at hs; exact absurd hs (by simp)

theorem frameStep?_init {n : ℕ} (c' : Fin n) (f : ℕ) (fr : Fin n → Option ℕ)
    (fr' : Fin n → Option ℕ) (hs : frameStep? (Event.INIT c' f) fr = some fr') :
    fr c' = none ∧ fr' = Function.update fr c' (some f) := by
  simp only [frameStep?] at hs
  by_cases hg : fr c' = none
  · rw [if_pos hg] at hs
    exact ⟨hg, (Option.some.inj hs).symm⟩
  · rw [if_neg hg] at hs; exact absurd hs (by simp)

theorem frameStep?_clear {n : ℕ} (c' : Fin n) (f : ℕ) (fr : Fin n → Option ℕ)
    (fr' : Fin n → Option ℕ) (hs : frameStep? (Event.CLEAR c' f) fr = some fr') :
    fr c' = some f ∧ fr' = Function.update fr c' none := by
  simp only [frameStep?] at hs
  by_cases hg : fr c' = some f
  · rw [if_pos hg] at hs
    exact ⟨hg, (Option.some.inj hs).symm⟩
  · rw [if_neg hg] at hs; exact absurd hs (by simp)

theorem w_move {n : ℕ} (c c' : Fin n) (s t : ℕ) : Writes (Event.MOVE c' s t) c ↔ c' = c := Iff.rfl
theorem w_init {n : ℕ} (c c' : Fin n) (f : ℕ) : Writes (Event.INIT c' f) c ↔ c' = c := Iff.rfl
theorem w_clear {n : ℕ} (c c' : Fin n) (f : ℕ) : Writes (Event.CLEAR c' f) c ↔ c' = c := Iff.rfl

/-- **The frame a column ends at is what its own track computes.** -/
theorem replayF?_track {n : ℕ} (p : List (Event n)) (fr : Fin n → Option ℕ) (c : Fin n)
    (g : Fin n → Option ℕ) (h : replayF? p fr = some g) :
    trackRun c p (fr c) = some (g c) := by
  induction p generalizing fr with
  | nil => simp [replayF?] at h; rw [← h]; rfl
  | cons e es ih =>
      rw [replayF?] at h
      cases hs : frameStep? e fr with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some fr' =>
          rw [hs] at h
          simp only [Option.bind_some] at h
          cases e with
          | MOVE c' s t =>
              by_cases hc : c' = c
              · obtain ⟨hg, hupd⟩ := frameStep?_move c' s t fr fr' hs
                have hgc : fr c = some s := by rw [← hc]; exact hg
                have hval : fr' c = some t := by rw [hupd, hc]; exact Function.update_self c (some t) fr
                simp only [trackRun, hc, hgc, if_true]
                rw [← hval]
                exact ih fr' h
              · have hfc : fr' c = fr c := frameStep?_other _ fr c (by simp [Writes, hc]) fr' hs
                simp only [trackRun, hc]
                rw [← hfc]
                exact ih fr' h
          | INIT c' f0 =>
              by_cases hc : c' = c
              · obtain ⟨hg, hupd⟩ := frameStep?_init c' f0 fr fr' hs
                have hgc : fr c = none := by rw [← hc]; exact hg
                have hval : fr' c = some f0 := by rw [hupd, hc]; exact Function.update_self c (some f0) fr
                simp only [trackRun, hc, hgc, if_true]
                rw [← hval]
                exact ih fr' h
              · have hfc : fr' c = fr c := frameStep?_other _ fr c (by simp [Writes, hc]) fr' hs
                simp only [trackRun, hc]
                rw [← hfc]
                exact ih fr' h
          | CLEAR c' f0 =>
              by_cases hc : c' = c
              · obtain ⟨hg, hupd⟩ := frameStep?_clear c' f0 fr fr' hs
                have hgc : fr c = some f0 := by rw [← hc]; exact hg
                have hval : fr' c = none := by rw [hupd, hc]; exact Function.update_self c none fr
                simp only [trackRun, hc, hgc, if_true]
                rw [← hval]
                exact ih fr' h
              · have hfc : fr' c = fr c := frameStep?_other _ fr c (by simp [Writes, hc]) fr' hs
                simp only [trackRun, hc]
                rw [← hfc]
                exact ih fr' h
          | SCALE c' f0 q =>
              have hfc : fr' c = fr c := frameStep?_other _ fr c (by simp [Writes]) fr' hs
              simp only [trackRun]
              rw [← hfc]
              exact ih fr' h
          | ADD d s q f0 =>
              have hfc : fr' c = fr c := frameStep?_other _ fr c (by simp [Writes]) fr' hs
              simp only [trackRun]
              rw [← hfc]
              exact ih fr' h



end Pr6453

/-- **The frame chart is the product of the per-column tracks.** -/
theorem Pr6453.chart_determined {n : ℕ} (p : List (Pr6453.Event n)) (fr : Fin n → Option ℕ)
    (g : Fin n → Option ℕ) (h : Pr6453.replayF? p fr = some g) (c : Fin n) :
    Pr6453.trackRun c p (fr c) = some (g c) :=
  Pr6453.replayF?_track p fr c g h

/-- **Each column's final frame is what its own track computes.** -/
theorem solution {n : ℕ} (p : List (Pr6453.Event n)) (fr : Fin n → Option ℕ) (c : Fin n)
    (g : Fin n → Option ℕ) (h : Pr6453.replayF? p fr = some g) :
    Pr6453.trackRun c p (fr c) = some (g c) :=
  Pr6453.replayF?_track p fr c g h
