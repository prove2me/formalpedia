-- Prove2me | solution 1 for Pr6453.replay_linear
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T22:18:01.868321+00:00
-- url     : https://prove2.me/submissions/e9910499-b670-4956-a4b1-c0f0f7e44fd0

/-
PR #6453: the output half — the rows are a linear function of the initial rows.
-/
import Definitions.Def_Pr6453_Replay
import Definitions.Def_Pr6453_Linear

set_option autoImplicit false

namespace Pr6453

theorem step?_MOVE {n : ℕ} (c : Fin n) (s t : ℕ) (st s' : State n)
    (h : step? (Event.MOVE c s t) st = some s') :
    st.frames c = some s ∧ s'.rows = st.rows ∧
      s'.frames = Function.update st.frames c (some t) := by
  simp only [step?] at h
  by_cases hg : st.frames c = some s
  · rw [if_pos hg] at h
    have := (Option.some.inj h).symm
    refine ⟨hg, ?_, ?_⟩
    · rw [this]
    · rw [this]
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem step?_INIT {n : ℕ} (c : Fin n) (f : ℕ) (st s' : State n)
    (h : step? (Event.INIT c f) st = some s') :
    st.frames c = none ∧ s'.rows = Function.update st.rows c 0 ∧
      s'.frames = Function.update st.frames c (some f) := by
  simp only [step?] at h
  by_cases hg : st.frames c = none
  · rw [if_pos hg] at h
    have := (Option.some.inj h).symm
    refine ⟨hg, ?_, ?_⟩ <;> rw [this]
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem step?_CLEAR {n : ℕ} (c : Fin n) (f : ℕ) (st s' : State n)
    (h : step? (Event.CLEAR c f) st = some s') :
    st.frames c = some f ∧ s'.rows = Function.update st.rows c 0 ∧
      s'.frames = Function.update st.frames c none := by
  simp only [step?] at h
  by_cases hg : st.frames c = some f
  · rw [if_pos hg] at h
    have := (Option.some.inj h).symm
    refine ⟨hg, ?_, ?_⟩ <;> rw [this]
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem step?_SCALE {n : ℕ} (c : Fin n) (f : ℕ) (q : ℚ) (st s' : State n)
    (h : step? (Event.SCALE c f q) st = some s') :
    st.frames c = some f ∧ s'.rows = Function.update st.rows c (q • st.rows c) ∧
      s'.frames = st.frames := by
  simp only [step?] at h
  by_cases hg : st.frames c = some f
  · rw [if_pos hg] at h
    have := (Option.some.inj h).symm
    refine ⟨hg, ?_, ?_⟩ <;> rw [this]
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem step?_ADD {n : ℕ} (d s : Fin n) (q : ℚ) (f : ℕ) (st s' : State n)
    (h : step? (Event.ADD d s q f) st = some s') :
    st.frames d = some f ∧ st.frames s = some f ∧
      s'.rows = Function.update st.rows d (st.rows d + q • st.rows s) ∧ s'.frames = st.frames := by
  simp only [step?] at h
  by_cases hg : st.frames d = some f ∧ st.frames s = some f
  · rw [if_pos hg] at h
    have := (Option.some.inj h).symm
    refine ⟨hg.1, hg.2, ?_, ?_⟩ <;> rw [this]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **A step is additive in the rows**: same frames, rows adding, and the results add. -/
theorem step?_add {n : ℕ} (e : Event n) (st₁ st₂ st₃ : State n)
    (hf : st₂.frames = st₁.frames) (ht : st₃.frames = st₁.frames)
    (hr : RowsAdd st₁.rows st₂.rows st₃.rows)
    (s₁ s₂ : State n) (h₁ : step? e st₁ = some s₁) (h₂ : step? e st₂ = some s₂) :
    ∃ s₃ : State n, step? e st₃ = some s₃ ∧ s₃.frames = s₁.frames ∧
      RowsAdd s₁.rows s₂.rows s₃.rows := by
  cases e with
  | MOVE c s t =>
      obtain ⟨g₁, r₁, f₁⟩ := step?_MOVE c s t st₁ s₁ h₁
      obtain ⟨g₂, r₂, f₂⟩ := step?_MOVE c s t st₂ s₂ h₂
      have g₂' : st₂.frames c = some s := g₂
      rw [hf] at g₂'
      refine ⟨{ st₃ with frames := Function.update st₃.frames c (some t) }, ?_, ?_, ?_⟩
      · simp only [step?]; rw [ht, g₁]; simp
      · simp only [f₁, f₂, ht]
      · intro i; simp only [r₁, r₂]
        exact hr i
  | INIT c f0 =>
      obtain ⟨g₁, r₁, f₁⟩ := step?_INIT c f0 st₁ s₁ h₁
      obtain ⟨g₂, r₂, f₂⟩ := step?_INIT c f0 st₂ s₂ h₂
      rw [hf] at g₂
      refine ⟨{ rows := Function.update st₃.rows c 0,
                frames := Function.update st₃.frames c (some f0) }, ?_, ?_, ?_⟩
      · simp only [step?]; rw [ht, g₁]; simp
      · simp only [f₁, f₂, ht]
      · intro i; simp only [r₁, r₂]
        by_cases hi : i = c
        · rw [hi]; simp
        · simp [Function.update, hi, hr i]
  | CLEAR c f0 =>
      obtain ⟨g₁, r₁, f₁⟩ := step?_CLEAR c f0 st₁ s₁ h₁
      obtain ⟨g₂, r₂, f₂⟩ := step?_CLEAR c f0 st₂ s₂ h₂
      rw [hf] at g₂
      refine ⟨{ rows := Function.update st₃.rows c 0, frames := Function.update st₃.frames c none }, ?_, ?_, ?_⟩
      · simp only [step?]; rw [ht, g₁]; simp
      · simp only [f₁, f₂, ht]
      · intro i; simp only [r₁, r₂]
        by_cases hi : i = c
        · rw [hi]; simp
        · simp [Function.update, hi, hr i]
  | SCALE c f0 q =>
      obtain ⟨g₁, r₁, f₁⟩ := step?_SCALE c f0 q st₁ s₁ h₁
      obtain ⟨g₂, r₂, f₂⟩ := step?_SCALE c f0 q st₂ s₂ h₂
      rw [hf] at g₂
      refine ⟨{ st₃ with rows := Function.update st₃.rows c (q • st₃.rows c) }, ?_, ?_, ?_⟩
      · simp only [step?]; rw [ht, g₁]; simp
      · simp only [f₁, f₂, ht]
      · intro i; simp only [r₁, r₂]
        by_cases hi : i = c
        · rw [hi]; simp [hr c, smul_add]
        · simp [Function.update, hi, hr i]
  | ADD d s q f0 =>
      obtain ⟨g₁, g₁', r₁, f₁⟩ := step?_ADD d s q f0 st₁ s₁ h₁
      obtain ⟨g₂, g₂', r₂, f₂⟩ := step?_ADD d s q f0 st₂ s₂ h₂
      rw [hf] at g₂ g₂'
      refine ⟨{ st₃ with rows := Function.update st₃.rows d (st₃.rows d + q • st₃.rows s) }, ?_, ?_, ?_⟩
      · simp only [step?]; rw [ht, g₁, g₁']; simp
      · simp only [f₁, f₂, ht]
      · intro i; simp only [r₁, r₂]
        by_cases hi : i = d
        · rw [hi]
          simp only [Function.update_self, hr d, hr s, smul_add]
          abel
        · simp [Function.update, hi, hr i]

/-- **Steps with equal frames produce equal frames.** -/
theorem step?_frames_eq {n : ℕ} (e : Event n) (st₁ st₂ : State n)
    (hf : st₂.frames = st₁.frames) (s₁ s₂ : State n)
    (h₁ : step? e st₁ = some s₁) (h₂ : step? e st₂ = some s₂) : s₂.frames = s₁.frames := by
  cases e with
  | MOVE c s t =>
      obtain ⟨-, -, f₁⟩ := step?_MOVE c s t st₁ s₁ h₁
      obtain ⟨-, -, f₂⟩ := step?_MOVE c s t st₂ s₂ h₂
      rw [f₁, f₂, hf]
  | INIT c f0 =>
      obtain ⟨-, -, f₁⟩ := step?_INIT c f0 st₁ s₁ h₁
      obtain ⟨-, -, f₂⟩ := step?_INIT c f0 st₂ s₂ h₂
      rw [f₁, f₂, hf]
  | CLEAR c f0 =>
      obtain ⟨-, -, f₁⟩ := step?_CLEAR c f0 st₁ s₁ h₁
      obtain ⟨-, -, f₂⟩ := step?_CLEAR c f0 st₂ s₂ h₂
      rw [f₁, f₂, hf]
  | SCALE c f0 q =>
      obtain ⟨-, -, f₁⟩ := step?_SCALE c f0 q st₁ s₁ h₁
      obtain ⟨-, -, f₂⟩ := step?_SCALE c f0 q st₂ s₂ h₂
      rw [f₁, f₂, hf]
  | ADD d s q f0 =>
      obtain ⟨-, -, -, f₁⟩ := step?_ADD d s q f0 st₁ s₁ h₁
      obtain ⟨-, -, -, f₂⟩ := step?_ADD d s q f0 st₂ s₂ h₂
      rw [f₁, f₂, hf]

/-- **The replay is additive in the rows.** -/
theorem replay?_add {n : ℕ} (p : List (Event n)) (st₁ st₂ st₃ : State n)
    (hf : st₂.frames = st₁.frames) (ht : st₃.frames = st₁.frames)
    (hr : RowsAdd st₁.rows st₂.rows st₃.rows)
    (s₁ s₂ : State n) (h₁ : replay? p st₁ = some s₁) (h₂ : replay? p st₂ = some s₂) :
    ∃ s₃ : State n, replay? p st₃ = some s₃ ∧ s₃.frames = s₁.frames ∧
      RowsAdd s₁.rows s₂.rows s₃.rows := by
  induction p generalizing st₁ st₂ st₃ s₁ s₂ with
  | nil =>
      simp only [replay?, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨st₃, rfl, ht, hr⟩
  | cons e es ih =>
      rw [replay?] at h₁ h₂
      cases h₁' : step? e st₁ with
      | none => rw [h₁'] at h₁; exact absurd h₁ (by simp)
      | some m₁ =>
          rw [h₁'] at h₁
          simp only [Option.bind_some] at h₁
          cases h₂' : step? e st₂ with
          | none => rw [h₂'] at h₂; exact absurd h₂ (by simp)
          | some m₂ =>
              rw [h₂'] at h₂
              simp only [Option.bind_some] at h₂
              obtain ⟨m₃, h₃', hf₃, hr₃⟩ := step?_add e st₁ st₂ st₃ hf ht hr m₁ m₂ h₁' h₂'
              have hf₂₁ : m₂.frames = m₁.frames := step?_frames_eq e st₁ st₂ hf m₁ m₂ h₁' h₂'
              obtain ⟨s₃, hs₃, hf₃', hr₃'⟩ := ih m₁ m₂ m₃ hf₂₁ hf₃ hr₃ s₁ s₂ h₁ h₂
              refine ⟨s₃, ?_, hf₃', hr₃'⟩
              rw [replay?, h₃']
              exact hs₃

/-- **The rows are a linear function of the initial rows**: two runs from the same frame chart,
with rows `a` and `b`, add up to a run with rows `a + b` ending at the sum of their rows. -/
theorem replay?_linear {n : ℕ} (p : List (Event n)) (fr : Fin n → Option ℕ)
    (a b : Fin n → ℕ →₀ ℚ) (s₁ s₂ : State n)
    (h₁ : replay? p ⟨a, fr⟩ = some s₁) (h₂ : replay? p ⟨b, fr⟩ = some s₂) :
    ∃ s₃ : State n, replay? p ⟨a + b, fr⟩ = some s₃ ∧ s₃.frames = s₁.frames ∧
      ∀ i, s₃.rows i = s₁.rows i + s₂.rows i := by
  have hr : RowsAdd (⟨a, fr⟩ : State n).rows (⟨b, fr⟩ : State n).rows (⟨a + b, fr⟩ : State n).rows :=
    fun i => rfl
  exact replay?_add p ⟨a, fr⟩ ⟨b, fr⟩ ⟨a + b, fr⟩ rfl rfl hr s₁ s₂ h₁ h₂

end Pr6453

/-- **The rows are a linear function of the initial rows.** -/
theorem solution {n : ℕ} (p : List (Pr6453.Event n)) (fr : Fin n → Option ℕ)
    (a b : Fin n → ℕ →₀ ℚ) (s₁ s₂ : Pr6453.State n)
    (h₁ : Pr6453.replay? p ⟨a, fr⟩ = some s₁) (h₂ : Pr6453.replay? p ⟨b, fr⟩ = some s₂) :
    ∃ s₃ : Pr6453.State n, Pr6453.replay? p ⟨a + b, fr⟩ = some s₃ ∧ s₃.frames = s₁.frames ∧
      ∀ i, s₃.rows i = s₁.rows i + s₂.rows i :=
  Pr6453.replay?_linear p fr a b s₁ s₂ h₁ h₂
