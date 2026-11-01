-- Prove2me | solution 1 for WilliamsonShmoys.finite_partial_order_has_maximal_above__p2m_93e678ee_21d2_4500_aea7_026ed25bc307_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:55:55.274335+00:00
-- url     : https://prove2.me/submissions/e6841750-56c4-4e54-b67f-d8053f8ba82f

import Mathlib

set_option autoImplicit false

theorem solution {α : Type} [Fintype α] (r : α → α → Prop)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hantisymm : ∀ a b, r a b → r b a → a = b)
    (a : α) :
    ∃ b, r a b ∧ ∀ c, r b c → c = b := by
  letI : Preorder α := {
    le := r
    le_refl := hrefl
    le_trans := htrans
  }
  classical
  obtain ⟨b, hab, hbmax⟩ :=
    (Finset.univ : Finset α).exists_le_maximal (Finset.mem_univ a)
  refine ⟨b, hab, fun c hbc => ?_⟩
  have hcb : r c b := hbmax.2 (Finset.mem_univ c) hbc
  exact (hantisymm b c hbc hcb).symm