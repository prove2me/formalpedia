-- Prove2me | solution 1 for YieldCheapTalk.Truthful.belief_truthful
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:57:16.256969+00:00
-- url     : https://prove2.me/submissions/9e8d9985-d290-4efa-8569-d615bb8eff8f

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

open YieldCheapTalk.Truthful in
theorem solution (M : Model) (hM : M.Standing) (Q : Level → Level → ℝ)
    (beta : Level → Level → Level → ℝ) (h : M.IsPBE id Q beta) :
    ∀ t m, beta t t m = 1 := by
  intro t m
  have h5 := h.2.2.2.2
  have hlam : 0 < M.lam t m := by
    unfold Model.lam
    apply div_pos (hM.p_pos t m)
    exact Finset.sum_pos (fun s _ => hM.p_pos s m) ⟨t, Finset.mem_univ t⟩
  have hs : ∑ s, (if id s = t then (1 : ℝ) else 0) * M.lam s m = M.lam t m := by
    simp
  have := h5 t m (by rw [hs]; exact hlam) t
  rw [this, hs]
  simp [hlam.ne']
