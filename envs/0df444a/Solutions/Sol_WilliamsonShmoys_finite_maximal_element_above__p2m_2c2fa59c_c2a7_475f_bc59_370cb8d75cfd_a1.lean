-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_element_above__p2m_2c2fa59c_c2a7_475f_bc59_370cb8d75cfd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:04:19.958864+00:00
-- url     : https://prove2.me/submissions/d071040c-d062-4c8c-8ea8-c789f59ecea4

import Theorems.Thm_WilliamsonShmoys_exists_maximal_of_finite
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution (α : Type) [Fintype α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) (hdown : ∀ ⦃x y : α⦄, x ≤ y → P y → P x) : ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b :=
  WilliamsonShmoys.exists_maximal_of_finite P a ha