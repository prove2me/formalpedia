-- Prove2me | solution 1 for SemigroupBetti.GenData.lemma16_PQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:22:34.754812+00:00
-- url     : https://prove2.me/submissions/811c90a1-64ca-4348-a432-b477a1f10dd3

module
public import Definitions.Def_SemigroupBetti_Arith
public import Definitions.Def_SemigroupBetti_Exceptional
public import Theorems.Thm_SemigroupBetti_GenData_exc_R
public import Theorems.Thm_SemigroupBetti_GenData_exc_nu_V2
public import Theorems.Thm_SemigroupBetti_GenData_sideQ_split
public import Theorems.Thm_SemigroupBetti_GenData_lemma14
public import Theorems.Thm_SemigroupBetti_GenData_lemma15
public import Theorems.Thm_SemigroupBetti_GenData_P_le
public import Theorems.Thm_SemigroupBetti_GenData_Q_le
public import Theorems.Thm_SemigroupBetti_GenData_compSupp_critVertex
public import Theorems.Thm_SemigroupBetti_GenData_mem_fam
public import Theorems.Thm_SemigroupBetti_GenData_sel_of_split
public import Theorems.Thm_SemigroupBetti_GenData_three_le_W


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (hA : G.A = 1) (hB : G.B = G.W - 1) : G.P + G.Q ≤ 2 * G.W - 5 := by
  have hW := G.three_le_W
  have hP := G.P_le
  have hQ := G.Q_le
  rw [exc_R hA hB] at hP hQ
  by_contra hc
  have hP' : G.P = G.W - 2 := by omega
  have hQ' : G.Q = G.W - 2 := by omega
  have hc2 := G.lemma14 hA hB hP'
  obtain ⟨⟨D, hD, hu⟩, hall⟩ := G.lemma15 hA hB hQ'
  have hsel := hall D hD hu
  have hK : ({1, 3} : Finset (Fin 4)).card = 2 := by decide
  have hDeq : D = G.crit 2 * G.n 2 := by
    rw [← (G.sel_of_split (G.sideQ_split hD) hK).1, hsel, exc_nu_V2 hA hB, hc2]
  obtain ⟨-, hcon, hS, -⟩ := G.mem_fam.1 hD
  subst hDeq
  exact hS ⟨_, by rw [G.compSupp_critVertex 2]; rfl⟩
end SemigroupBetti.GenData
