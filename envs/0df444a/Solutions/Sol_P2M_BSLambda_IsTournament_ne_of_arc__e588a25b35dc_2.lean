-- Prove2me | solution 2 for P2M_BSLambda_IsTournament_ne_of_arc__e588a25b35dc
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:50:28.620155+00:00
-- url     : https://prove2.me/submissions/f4f83147-8ed4-410d-9655-67b9ed78a20f

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
open BSLambda.IsTournament
variable {Arc : ι → ι → Bool} (h : IsTournament Arc) {i j : ι}
include h


theorem solution (hij : Arc i j) : j ≠ i := by
  rintro rfl; simp [h.arc_self] at hij
