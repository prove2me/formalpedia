-- Prove2me | solution 1 for SemigroupBetti.GenData.beta1_le_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:22:22.915801+00:00
-- url     : https://prove2.me/submissions/446fccf6-f232-4b32-8359-a80bd7bfb251

module
public import Definitions.Def_SemigroupBetti_Antichain
public import Definitions.Def_SemigroupBetti_Arith
public import Theorems.Thm_SemigroupBetti_GenData_E_le
public import Theorems.Thm_SemigroupBetti_GenData_P_le
public import Theorems.Thm_SemigroupBetti_GenData_Q_le
public import Theorems.Thm_SemigroupBetti_GenData_beta1_eq
public import Theorems.Thm_SemigroupBetti_GenData_sigma_le_four


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.beta1 ≤ 4 + 2 * (G.R - 1) + (G.p + G.q - 1) := by
  rw [G.beta1_eq]
  have := G.sigma_le_four
  have := G.P_le
  have := G.Q_le
  have := G.E_le
  omega
end SemigroupBetti.GenData
