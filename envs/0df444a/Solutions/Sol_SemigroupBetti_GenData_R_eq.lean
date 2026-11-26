-- Prove2me | solution 1 for SemigroupBetti.GenData.R_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:02:35.263799+00:00
-- url     : https://prove2.me/submissions/30a08a1d-8655-4528-a603-6a68e5a4305e

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_A_lt_B
public import Theorems.Thm_SemigroupBetti_GenData_B_lt_W


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.R = G.W - max G.s G.t := by
  have := G.A_lt_B; have := G.B_lt_W; unfold R s t; omega
end SemigroupBetti.GenData
