-- Prove2me | solution 1 for P2M_BSLambda_IsTournament_ne_of_arc__e588a25b35dc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:50:16.716494+00:00
-- url     : https://prove2.me/submissions/5035a7c0-bc06-44db-adc3-f744ff8c6166

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsTournament_ne_of_arc

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
open BSLambda.IsTournament
variable {Arc : ι → ι → Bool} (h : IsTournament Arc) {i j : ι}
include h
namespace BSLambda.IsTournament
theorem _root_.solution (hij : Arc i j) : j ≠ i := (h.ne_of_arc hij).symm
end BSLambda.IsTournament
