-- Prove2me | solution 1 for PochetWolsey.Variants.combined_formulation_solves
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:28:27.161985+00:00
-- url     : https://prove2.me/submissions/17c3e42c-5132-48a3-9694-255c64f39f9c

import Mathlib
import Definitions.Def_PochetWolsey_Variants_CombinedModel

open PochetWolsey.Variants

theorem solution : ¬ (∀ {n K L : ℕ} (D : CombinedData n K L)
    (hD : D.Standing),
    ∃ w q : CombinedPoint n K L,
      IsMinimum D.original D.cost w ∧ IsMinimum D.extended D.cost q ∧
      D.cost w = D.cost q) := by
  intro H
  let D : CombinedData 2 1 1 :=
    ⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ![0, -1, 0], fun _ => 0, 1⟩
  have hD : D.Standing := by
    refine ⟨by norm_num, by norm_num, by norm_num, fun _ => le_rfl, fun _ _ => le_rfl,
      fun _ _ => ⟨le_rfl, le_rfl⟩, fun _ _ _ _ => ⟨le_rfl, le_rfl⟩, fun _ _ _ _ => le_rfl,
      one_pos, by simp [D]⟩
  obtain ⟨w, -, ⟨hw, hmin⟩, -, -⟩ := H D hD
  obtain ⟨⟨hdx, hdv, hdsr, hs0, hs2, hr0, hr2⟩, hbal, hv, hx⟩ := hw
  let w' : CombinedPoint 2 1 1 :=
    ⟨w.x, w.y, w.v, fun i => w.s i + if i = 1 then 1 else 0, fun i => w.r i + if i = 1 then 1 else 0⟩
  have hw' : D.original w' := by
    refine ⟨⟨hdx, hdv, ?_, ?_, ?_, ?_, ?_⟩, ?_, hv, hx⟩
    · intro t
      have := hdsr t
      constructor <;> (simp only [w']; split_ifs <;> linarith)
    · simp [w', hs0]
    · simp [w']; exact hs2
    · simp [w', hr0]
    · simp [w']; exact hr2
    · intro t
      have := hbal t
      fin_cases t <;> simp [w'] at this ⊢ <;> linarith
  have hc := hmin w' hw'
  simp [CombinedData.cost, D, w', Fin.sum_univ_succ] at hc
  linarith
