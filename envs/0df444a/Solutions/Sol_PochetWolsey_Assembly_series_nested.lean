-- Prove2me | solution 1 for PochetWolsey.Assembly.series_nested
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:50:19.197003+00:00
-- url     : https://prove2.me/submissions/a002fc18-2937-4ead-ad4d-cbae9d326484

import Mathlib
import Definitions.Def_PochetWolsey_Assembly_Model

open PochetWolsey.Assembly

theorem solution : ¬ (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (I : Model m n) (hseries : IsSeries I)
    (hcost : (WagnerWhitin I ∧ NonincreasingSetups I) ∨ StationaryCosts I),
    ∃ a : Plan m n, Optimal I none a ∧ Nested I a) := by
  intro H
  let I : Model 1 2 := ⟨fun _ => 0, rfl, fun i hi => by
      simp only [Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hi (Fin.ext h)), ![0, 1],
    by intro t; fin_cases t <;> simp, fun _ _ => 0,
    fun i _ => if i.val = 0 then 1 else -1, fun _ _ => 0⟩
  let a0 : Plan 1 2 := ⟨fun i t => if (i.val = 0 ∧ t.val = 1) ∨ (i.val = 1 ∧ t.val = 0) then 1 else 0,
      fun i t => if i.val = 1 ∧ t.val = 1 then 1 else 0, fun _ _ => true⟩
  have hfeas : Feasible I none a0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i t; fin_cases i <;> fin_cases t <;> simp [a0]
    · intro i t; fin_cases i <;> fin_cases t <;> simp [a0]
    · intro i; fin_cases i <;> simp [a0, Fin.last]
    · intro i t; fin_cases i <;> fin_cases t <;> simp [a0, I, effectiveDemand]
    · intro i t h; simp [a0] at h
    · intro C' hC; cases hC
  have hc0 : cost I a0 = -1 := by
    simp [cost, Fin.sum_univ_succ, I, a0]
  have hser : IsSeries I := by
    intro i hi
    have : i = 1 := by fin_cases i <;> simp_all
    subst this; rfl
  have hstat : StationaryCosts I := by
    refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨a, ⟨ha, hopt⟩, hnest⟩ := H (by norm_num) (by norm_num) I hser (Or.inr hstat)
  have hle := hopt a0 hfeas
  rw [hc0] at hle
  obtain ⟨hx, hs, hend, hflow, -, -⟩ := ha
  have f00 := hflow 0 0
  have f01 := hflow 0 1
  have f10 := hflow 1 0
  have f11 := hflow 1 1
  have e0 := hend 0
  have e1 := hend 1
  have x00 := hx 0 0
  have x11 := hx 1 1
  simp [effectiveDemand, I, Fin.last] at f00 f01 f10 f11 e0 e1
  simp [cost, Fin.sum_univ_succ, I] at hle
  have hpos : 0 < a.production 1 0 := by
    linarith [e0.1, e0.2, e1.1, e1.2, hs 0 1, hs 1 1]
  have := hnest 1 0 (by decide) hpos
  have h00 : a.production 0 0 = 0 := by
    linarith [e0.1, e0.2, e1.1, e1.2, hs 0 1, hs 1 1]
  simp [I, h00] at this
