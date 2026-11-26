-- Prove2me | solution 1 for SemigroupBetti.GenData.p_mul_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:11:30.106898+00:00
-- url     : https://prove2.me/submissions/bdc9e77a-0edc-4480-bd16-bc4e69ce191f

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_dg_pos
public import Theorems.Thm_SemigroupBetti_GenData_dg_mul_p
public import Theorems.Thm_SemigroupBetti_GenData_dg_mul_q

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.p * G.A = G.q * G.t := by
  have h : G.dg * (G.p * G.A) = G.dg * (G.q * G.t) := by
    calc G.dg * (G.p * G.A) = (G.dg * G.p) * G.A := by ring
      _ = G.t * (G.dg * G.q) := by rw [G.dg_mul_p, G.dg_mul_q]; rfl
      _ = G.dg * (G.q * G.t) := by ring
  exact Nat.eq_of_mul_eq_mul_left G.dg_pos h
end SemigroupBetti.GenData
