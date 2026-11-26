-- Prove2me | solution 1 for SemigroupBetti.GenData.beta1_le_two_W_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:23:54.577664+00:00
-- url     : https://prove2.me/submissions/bf5e2faf-1c25-4b28-807a-a0ce07d8e472

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_exc_p
public import Theorems.Thm_SemigroupBetti_GenData_exc_q
public import Theorems.Thm_SemigroupBetti_GenData_lemma16_PQ
public import Theorems.Thm_SemigroupBetti_GenData_E_le
public import Theorems.Thm_SemigroupBetti_GenData_beta1_eq
public import Theorems.Thm_SemigroupBetti_GenData_sigma_le_four
public import Theorems.Thm_SemigroupBetti_GenData_three_le_W


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (hA : G.A = 1) (hB : G.B = G.W - 1) :
    G.beta1 ≤ 2 * G.W := by
  have hW := G.three_le_W
  have hPQ := G.lemma16_PQ hA hB
  have hE := G.E_le
  rw [exc_p hA hB, exc_q hA hB] at hE
  have hσ := G.sigma_le_four
  rw [G.beta1_eq]
  omega
end SemigroupBetti.GenData
