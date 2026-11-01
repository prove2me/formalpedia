-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_extension__p2m_9df70f0c_e392_4539_bc07_082cd2cf5417_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:47:29.187216+00:00
-- url     : https://prove2.me/submissions/4e962643-ff6d-4c18-b74d-b09efd972015

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) {a : α} (ha : P a) :
    ∃ b, a ≤ b ∧ P b ∧ ∀ c, b ≤ c → P c → c ≤ b := by
  classical
  obtain ⟨b, hab, hbmax⟩ :=
    (Set.toFinite {x : α | P x}).exists_le_maximal (s := {x : α | P x}) ha
  exact ⟨b, hab, hbmax.1, fun c hbc hc => hbmax.2 hc hbc⟩