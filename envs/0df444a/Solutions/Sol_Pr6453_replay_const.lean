-- Prove2me | solution 1 for Pr6453.replay_const
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T21:41:04.122689+00:00
-- url     : https://prove2.me/submissions/35befeea-fdcf-450e-b777-0a517b8cd5d7

/-
PR #6453: locality of the frame chart.
-/
import Definitions.Def_Pr6453_Frames
import Definitions.Def_Pr6453_Locality

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

theorem replayF?_const {n : ℕ} (p : List (Event n)) (fr : Fin n → Option ℕ) (c : Fin n)
    (hw : ∀ e ∈ p, ¬ Writes e c) (g : Fin n → Option ℕ) (h : replayF? p fr = some g) :
    g c = fr c := by
  induction p generalizing fr with
  | nil => simp [replayF?] at h; rw [← h]
  | cons e es ih =>
      rw [replayF?] at h
      cases hs : frameStep? e fr with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some fr' =>
          rw [hs] at h
          simp only [Option.bind_some] at h
          have he : ¬ Writes e c := hw e (List.mem_cons_self ..)
          have hes : ∀ e' ∈ es, ¬ Writes e' c := fun e' he' => hw e' (List.mem_cons_of_mem _ he')
          have hfc : fr' c = fr c := frameStep?_other e fr c he fr' hs
          rw [ih fr' hes h, hfc]

end Pr6453

/-- **A program that never writes a column leaves its frame alone.** -/
theorem solution {n : ℕ} (p : List (Pr6453.Event n)) (fr : Fin n → Option ℕ) (c : Fin n)
    (hw : ∀ e ∈ p, ¬ Pr6453.Writes e c) (g : Fin n → Option ℕ)
    (h : Pr6453.replayF? p fr = some g) : g c = fr c :=
  Pr6453.replayF?_const p fr c hw g h
