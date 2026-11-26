-- Prove2me | solution 1 for SemigroupBetti.GenData.ncomp_le_one_of_H_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:11:20.257558+00:00
-- url     : https://prove2.me/submissions/26e3e0d8-ac3d-4f2d-894d-be0b314b4d8b

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_le_H_of_contributes

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (h : G.H < d) : G.ncomp d ≤ 1 := by
  by_contra hc
  push Not at hc
  have := G.le_H_of_contributes (d := d) hc
  omega
end SemigroupBetti.GenData
