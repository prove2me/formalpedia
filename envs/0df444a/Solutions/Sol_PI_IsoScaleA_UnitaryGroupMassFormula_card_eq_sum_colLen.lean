-- Prove2me | solution 1 for PI.IsoScaleA.UnitaryGroupMassFormula.card_eq_sum_colLen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:44:16.691984+00:00
-- url     : https://prove2.me/submissions/f05aab82-bab9-42b1-9826-8e083e26505a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoScaleA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryScaleCount_CardEqSumColLen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoScaleA PI.IsoScaleA.UnitaryGroupMassFormula
open PI.IsoScaleA
namespace PI.IsoScaleA.UnitaryGroupMassFormula
theorem _root_.solution (μ : YoungDiagram) :
    μ.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  classical
  rw [← Finset.sum_range (fun j => μ.colLen j)]
  have hmaps : ((μ.cells : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).MapsTo Prod.snd
      (Finset.range (μ.rowLen 0)) := by
    intro x hx
    have hx' : (x.1, x.2) ∈ μ := hx
    have h0 : (0, x.2) ∈ μ := μ.up_left_mem (Nat.zero_le _) le_rfl hx'
    simpa [Finset.mem_range] using YoungDiagram.mem_iff_lt_rowLen.mp h0
  rw [YoungDiagram.card, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (μ.cells.filter fun x => x.2 = j) =
      (Finset.range (μ.colLen j)).map ⟨fun i => (i, j), fun a b h => by simpa using h⟩ := by
    ext ⟨i, k⟩
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_range]
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨i, YoungDiagram.mem_iff_lt_colLen.mp h1, rfl⟩
    · rintro ⟨a, ha, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (a, j) = (i, k) from h)
      exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr ha, rfl⟩
  rw [this, Finset.card_map, Finset.card_range]
end PI.IsoScaleA.UnitaryGroupMassFormula
