-- Prove2me | solution 1 for SemigroupBetti.GenData.p_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:03:40.374432+00:00
-- url     : https://prove2.me/submissions/d568a05f-ea7e-46ed-99ee-4a014b827807

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_t_pos
public import Theorems.Thm_SemigroupBetti_GenData_dg_mul_p

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 1 ≤ G.p := by
  have h := G.dg_mul_p; have := G.t_pos
  rcases Nat.eq_zero_or_pos G.p with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0
end SemigroupBetti.GenData
