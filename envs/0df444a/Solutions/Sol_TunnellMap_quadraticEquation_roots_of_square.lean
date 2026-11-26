-- Prove2me | solution 1 for TunnellMap.quadraticEquation_roots_of_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:23.782382+00:00
-- url     : https://prove2.me/submissions/c52e7bc1-336d-4ac3-94db-a1c8739e986b

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots
import Theorems.Thm_TunnellMap_quadraticEquation_iff_root_certificate
import Theorems.Thm_TunnellMap_integer_square_roots
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {α c d s a : ℤ}
    (hα : α ≠ 0) (hs : s ^ 2 = quadraticHalfDiscriminant α c d) :
    quadraticEquation α c d a ↔
      (α * a = -c + s ∨ α * a = -c - s) := by
  rw [quadraticEquation_iff_root_certificate hα]
  constructor
  · rintro ⟨u, hu, ha⟩
    rcases integer_square_roots (hu.trans hs.symm) with huEq | huEq
    · left
      simpa [huEq] using ha
    · right
      rw [huEq] at ha
      linarith
  · intro h
    rcases h with h | h
    · exact ⟨s, hs, h⟩
    · refine ⟨-s, by simpa using hs, ?_⟩
      linarith
end TunnellMap
