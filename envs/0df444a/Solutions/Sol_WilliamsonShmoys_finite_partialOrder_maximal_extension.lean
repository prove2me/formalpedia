-- Prove2me | solution 1 for WilliamsonShmoys.finite_partialOrder_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:42:12.438217+00:00
-- url     : https://prove2.me/submissions/0a90bd7b-3232-4a33-a2a9-305481c80648

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧
      ∀ c : α, P c → b ≤ c → b = c := by
  obtain ⟨b, ⟨hab, hPb⟩, hmax⟩ := Set.Finite.exists_maximal
    (s := {x : α | a ≤ x ∧ P x}) (Set.toFinite _) ⟨a, le_rfl, ha⟩
  exact ⟨b, hab, hPb, fun c hPc hbc => le_antisymm hbc (hmax ⟨le_trans hab hbc, hPc⟩ hbc)⟩
