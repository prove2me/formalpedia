-- Prove2me | solution 1 for WilliamsonShmoys.twoPointFiber_step_orbit__p2m_9753acd4_210b_4775_9b9c_ae60e8780cc8_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:22:17.399307+00:00
-- url     : https://prove2.me/submissions/f0416578-f4ef-4aef-9496-d0e6010379e3

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {X V : Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]
    (tail : X → V) (step : X → X)
    (hPres : ∀ x, tail (step x) = tail x)
    (hNoFix : ∀ x, step x ≠ x)
    (hCard : ∀ v, Fintype.card {x : X // tail x = v} = 2) :
    ∀ x y, tail x = tail y → ∃ k : Nat, step^[k] x = y := by
  intro x y hxy
  by_cases hxy' : x = y
  · subst y
    exact ⟨0, by simp⟩
  · let sx : {w : X // tail w = tail x} := ⟨x, rfl⟩
    let sy : {w : X // tail w = tail x} := ⟨y, hxy.symm⟩
    have hS : Fintype.card {w : X // tail w = tail x} = 2 := hCard (tail x)
    have hsxy : sx ≠ sy := by
      intro h
      apply hxy'
      simpa [sx, sy] using congrArg (fun z : {w : X // tail w = tail x} => z.1) h
    have hall : ∀ z : {w : X // tail w = tail x}, z = sx ∨ z = sy := by
      intro z
      by_contra hz
      simp only [not_or] at hz
      have hxz : sx ≠ z := fun h => hz.1 h.symm
      have hyz : sy ≠ z := fun h => hz.2 h.symm
      let t : Finset {w : X // tail w = tail x} := {sx, sy, z}
      have ht3 : t.card = 3 := by
        simp [t, hsxy, hxz, hyz]
      have hle : t.card ≤ Fintype.card {w : X // tail w = tail x} :=
        Finset.card_le_univ t
      omega
    let ss : {w : X // tail w = tail x} := ⟨step x, hPres x⟩
    have hss_ne : ss ≠ sx := by
      intro h
      apply hNoFix x
      simpa [ss, sx] using congrArg (fun z : {w : X // tail w = tail x} => z.1) h
    have hss : ss = sy := by
      rcases hall ss with h | h
      · exact (hss_ne h).elim
      · exact h
    have hstep : step x = y := by
      simpa [ss, sy] using congrArg (fun z : {w : X // tail w = tail x} => z.1) hss
    exact ⟨1, by simpa using hstep⟩
