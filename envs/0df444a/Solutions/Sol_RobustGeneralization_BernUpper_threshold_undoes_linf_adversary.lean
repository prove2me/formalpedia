-- Prove2me | solution 1 for RobustGeneralization.BernUpper.threshold_undoes_linf_adversary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:36:52.055542+00:00
-- url     : https://prove2.me/submissions/97f083c9-1454-4f6e-bf1b-a064de564ca1

import Mathlib
import Definitions.Def_RobustGeneralization_BernUpper_Model

namespace RobustGeneralization.BernUpper

theorem aux_thrlinf_coord {d : ℕ} (s : Fin d → Bool) (ε : ℝ) (hε1 : ε < 1)
    (x' : E d) (hx : x' ∈ linfBall (pm s) ε) : thr x' = pm s := by
  ext i
  have h := hx i
  simp only [thr, pm, PiLp.toLp_apply] at h ⊢
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  cases hs : s i
  · have hl : lab false = -1 := by simp [lab]
    rw [hs, hl] at h1 h2
    rw [hl, if_neg (by linarith)]
  · have hl : lab true = 1 := by simp [lab]
    rw [hs, hl] at h1 h2
    rw [hl, if_pos (by linarith)]

end RobustGeneralization.BernUpper

open RobustGeneralization.BernUpper

theorem solution {d : ℕ} (s : Fin d → Bool) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    thr '' linfBall (pm s) ε = {pm s} := by
  ext y
  simp only [Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact aux_thrlinf_coord s ε hε1 x' hx'
  · rintro rfl
    have hmem : pm s ∈ linfBall (pm s) ε := by
      intro i
      simp [hε0]
    exact ⟨pm s, hmem, aux_thrlinf_coord s ε hε1 (pm s) hmem⟩
