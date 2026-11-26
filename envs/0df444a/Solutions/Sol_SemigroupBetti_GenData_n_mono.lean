-- Prove2me | solution 1 for SemigroupBetti.GenData.n_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:09.810907+00:00
-- url     : https://prove2.me/submissions/98f1d1d7-f804-4d1c-ab82-d377333f57f4

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_n_strictMono

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : Monotone G.n := G.n_strictMono.monotone
end SemigroupBetti.GenData
