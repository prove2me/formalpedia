-- Prove2me | solution 1 for SemigroupBetti.GenData.q_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:10:47.726975+00:00
-- url     : https://prove2.me/submissions/10104d99-1e6f-4c3f-b953-dda865394fb3

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_s_pos
public import Theorems.Thm_SemigroupBetti_GenData_dg_mul_q

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : 1 ≤ G.q := by
  have h := G.dg_mul_q; have := G.s_pos
  rcases Nat.eq_zero_or_pos G.q with h0 | h0
  · rw [h0, mul_zero] at h; omega
  · exact h0
end SemigroupBetti.GenData
