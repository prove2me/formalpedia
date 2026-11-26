-- Prove2me | solution 1 for SemigroupBetti.GenData.general_bound_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:12:27.333248+00:00
-- url     : https://prove2.me/submissions/74bf3192-a643-4330-ae1b-0172782d37ff

module
public import Definitions.Def_SemigroupBetti_Antichain
public import Definitions.Def_SemigroupBetti_Arith
public import Theorems.Thm_SemigroupBetti_GenData_R_eq
public import Theorems.Thm_SemigroupBetti_GenData_p_add_q_eq
public import Theorems.Thm_SemigroupBetti_GenData_p_pos
public import Theorems.Thm_SemigroupBetti_GenData_two_le_R


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution :
    4 + 2 * (G.R - 1) + (G.p + G.q - 1) = 2 * G.W - 2 * max G.s G.t + (G.s + G.t) / G.dg + 1 := by
  rw [← G.p_add_q_eq, G.R_eq]
  have := G.two_le_R; rw [G.R_eq] at this
  have := G.p_pos
  omega
end SemigroupBetti.GenData
