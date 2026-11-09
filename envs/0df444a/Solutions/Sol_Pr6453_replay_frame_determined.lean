-- Prove2me | solution 1 for Pr6453.replay_frame_determined
-- status  : ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T20:59:07.060333+00:00
-- url     : https://prove2.me/submissions/8a22e01a-5a57-47e7-bd57-0c2df9a818b5

/-
PR #6453: the replay is frame-determined.
-/
import Definitions.Def_Pr6453_Replay
import Definitions.Def_Pr6453_Frames

set_option autoImplicit false

namespace Pr6453

theorem step?_frames {n : ℕ} (e : Event n) (st : State n) :
    (step? e st).map (fun s => s.frames) = frameStep? e st.frames := by
  cases e with
  | MOVE c s t => by_cases h : st.frames c = some s <;> simp [step?, frameStep?, h]
  | INIT c f => by_cases h : st.frames c = none <;> simp [step?, frameStep?, h]
  | CLEAR c f => by_cases h : st.frames c = some f <;> simp [step?, frameStep?, h]
  | SCALE c f q => by_cases h : st.frames c = some f <;> simp [step?, frameStep?, h]
  | ADD d s q f => by_cases h : st.frames d = some f ∧ st.frames s = some f <;>
      simp [step?, frameStep?, h]

theorem step?_isSome {n : ℕ} (e : Event n) (st : State n) :
    (step? e st).isSome = (frameStep? e st.frames).isSome := by
  conv_lhs => rw [← Option.isSome_map (f := fun s : State n => s.frames)]
  rw [step?_frames]

theorem replay_frame_determined {n : ℕ} (prog : List (Event n)) (st : State n) :
    (replay? prog st).isSome = (replayF? prog st.frames).isSome := by
  induction prog generalizing st with
  | nil => rfl
  | cons e es ih =>
      have key : ∀ (st' : State n), step? e st = some st' →
          (replay? es st').isSome = (replayF? es st'.frames).isSome := fun st' _ => ih st'
      cases hs : step? e st with
      | none =>
          have hf : frameStep? e st.frames = none := by
            have h := step?_isSome e st
            rw [hs] at h
            simpa using h.symm
          simp only [replay?, replayF?, hs, hf]
          rfl
      | some st' =>
          have hf : frameStep? e st.frames = some st'.frames := by
            have h := step?_frames e st
            rw [hs] at h
            exact h.symm
          simp only [replay?, replayF?, hs, hf]
          exact key st' hs

end Pr6453

/-- **The replay is frame-determined.** -/
theorem solution {n : ℕ} (prog : List (Pr6453.Event n)) (st : Pr6453.State n) :
    (Pr6453.replay? prog st).isSome = (Pr6453.replayF? prog st.frames).isSome :=
  Pr6453.replay_frame_determined prog st
