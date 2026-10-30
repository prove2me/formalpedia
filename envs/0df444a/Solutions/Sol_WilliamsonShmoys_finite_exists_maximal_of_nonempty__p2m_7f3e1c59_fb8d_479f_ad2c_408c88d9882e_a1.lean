-- Prove2me | solution 1 for WilliamsonShmoys.finite_exists_maximal_of_nonempty__p2m_7f3e1c59_fb8d_479f_ad2c_408c88d9882e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:19:48.939649+00:00
-- url     : https://prove2.me/submissions/040d5470-02d2-4516-8816-7fa6927a3456

import Mathlib

set_option autoImplicit false

theorem solution
    {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop)
    (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by
  classical
  obtain ⟨w, hw⟩ := hP
  obtain ⟨a, ha, hmax⟩ :=
    ({a : α | P a} : Set α).toFinite.exists_maximal ⟨w, hw⟩
  exact ⟨a, ha, fun b hb hab => hmax hb hab⟩