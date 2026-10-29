-- Prove2me | solution 1 for PochetWolsey.Assembly.assembly_nested
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:30:24.882093+00:00
-- url     : https://prove2.me/submissions/8e0971d2-ee9d-48cb-add6-fa0c8d342742

import Mathlib
import Definitions.Def_PochetWolsey_Assembly_Model

open PochetWolsey.Assembly

theorem solution : ¬ (∀ {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (I : Model m n) (c : Option (Capacity m n))
    (hfeasible : ∃ a : Plan m n, Feasible I c a)
    (hww : WagnerWhitin I) (hsetup : NonincreasingSetups I),
    ∃ a : Plan m n, Optimal I c a ∧ Nested I a) := by
  intro H
  let I : Model 1 2 := ⟨fun _ => 0, rfl, fun i hi => by
      simp only [Fin.val_zero]; exact Nat.pos_of_ne_zero (fun h => hi (Fin.ext h)), ![0, 1],
    by intro t; fin_cases t <;> simp, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩
  let C : Capacity 1 2 := fun i t =>
    if (i.val = 0 ∧ t.val = 1) ∨ (i.val = 1 ∧ t.val = 0) then 1 else 0
  let a0 : Plan 1 2 := ⟨fun i t => if (i.val = 0 ∧ t.val = 1) ∨ (i.val = 1 ∧ t.val = 0) then 1 else 0,
      fun i t => if i.val = 1 ∧ t.val = 1 then 1 else 0, fun _ _ => true⟩
  have hfeas : Feasible I (some C) a0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i t; fin_cases i <;> fin_cases t <;> simp [a0]
    · intro i t; fin_cases i <;> fin_cases t <;> simp [a0]
    · intro i; fin_cases i <;> simp [a0, Fin.last]
    · intro i t; fin_cases i <;> fin_cases t <;> simp [a0, I, effectiveDemand]
    · intro i t h; simp [a0] at h
    · intro C' hC i t; cases hC; fin_cases i <;> fin_cases t <;> simp [a0, C]
  obtain ⟨a, ⟨ha, -⟩, hnest⟩ := H (by norm_num) (by norm_num) I (some C) ⟨a0, hfeas⟩
    (by intro i t u _; simp [echelonHolding, I]) (by intro i t u _; simp [I])
  obtain ⟨hx, hs, hend, hflow, -, hcap⟩ := ha
  have c00 := hcap C rfl 0 0
  have c11 := hcap C rfl 1 1
  have f00 := hflow 0 0
  have f01 := hflow 0 1
  have f10 := hflow 1 0
  have f11 := hflow 1 1
  have e0 := hend 0
  have e1 := hend 1
  have x00 := hx 0 0
  have x11 := hx 1 1
  simp [C, effectiveDemand, I, Fin.last] at c00 c11 f00 f01 f10 f11 e0 e1
  have hpos : 0 < a.production 1 0 := by
    linarith [e0.1, e0.2, e1.1, e1.2]
  have := hnest 1 0 (by decide) hpos
  have h00 : a.production 0 0 = 0 := by linarith
  simp [I, h00] at this
