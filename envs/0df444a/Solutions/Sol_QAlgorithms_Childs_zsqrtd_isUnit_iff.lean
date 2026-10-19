-- Prove2me | solution 1 for QAlgorithms.Childs.zsqrtd_isUnit_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:16:59.476479+00:00
-- url     : https://prove2.me/submissions/f1c7d5f9-42c7-4857-83b9-f3edbd642488

import Definitions.Def_QAlgorithms_Defs_Basic
set_option autoImplicit false

theorem solution (d : ℤ) (hd_sqfree : Squarefree d) (hd : 2 ≤ d) (x y : ℤ) :
    IsUnit (⟨x, y⟩ : ℤ√d) ↔ x ^ 2 - d * y ^ 2 = 1 ∨ x ^ 2 - d * y ^ 2 = -1 := by
  rw [Zsqrtd.isUnit_iff_norm_isUnit, Int.isUnit_iff]
  simp only [Zsqrtd.norm, pow_two]
  ring_nf
