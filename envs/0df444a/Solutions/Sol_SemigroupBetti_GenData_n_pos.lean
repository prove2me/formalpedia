-- Prove2me | solution 1 for SemigroupBetti.GenData.n_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:31:17.744349+00:00
-- url     : https://prove2.me/submissions/ebe3a6f5-8048-464e-bc62-0eed80550a4d

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_GenData_m_le_n

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (i : Fin 4) : 0 < G.n i := lt_of_lt_of_le G.m_pos (G.m_le_n i)
end SemigroupBetti.GenData
