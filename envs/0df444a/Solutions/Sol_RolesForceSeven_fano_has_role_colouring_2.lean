-- Prove2me | solution 2 for RolesForceSeven.fano_has_role_colouring
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-24T10:10:46.629237+00:00
-- url     : https://prove2.me/submissions/008d40d2-a6bb-429c-a79a-533e2d3957fe

import Mathlib
import Definitions.Def_RolesForceSeven_fano

open RolesForceSeven

set_option maxRecDepth 100000 in
theorem solution : ∃ role, RoleColouring fano role := by
  refine ⟨fun x l => if l = fanoLine x then 0 else if l = fanoLine (x - 1) then 1 else 2, ?_⟩
  unfold RoleColouring
  simp only [fano, Finset.forall_mem_image, Finset.exists_mem_image, Finset.mem_univ,
    true_and, forall_const]
  decide
