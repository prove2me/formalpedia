-- Prove2me | solution 1 for SemigroupBetti.GenData.E_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:21:03.668877+00:00
-- url     : https://prove2.me/submissions/a6ac2eb4-9c2e-44c9-877c-71b067743fa1

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_IsPairAntichain_exists_rank
public import Theorems.Thm_SemigroupBetti_GenData_not_dominates_pq
public import Theorems.Thm_SemigroupBetti_GenData_card_pairsE
public import Theorems.Thm_SemigroupBetti_GenData_pairsE_antichain
public import Theorems.Thm_SemigroupBetti_GenData_pairsE_pos
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_p_pos
public import Theorems.Thm_SemigroupBetti_GenData_q_pos
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.E ≤ G.p + G.q - 1 := by
  by_contra hc
  have hp := G.p_pos
  have hq := G.q_pos
  have hk : G.p + G.q ≤ G.pairsE.card := by rw [card_pairsE]; omega
  obtain ⟨x, hx, hx1, hx2⟩ :=
    G.pairsE_antichain.exists_rank G.pairsE_pos (r := G.p) hp (by omega)
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  exact G.not_dominates_pq hd hx1 (by simp only at hx2; omega)
    (fun h => by simp only [Prod.mk.injEq] at h; simp only at hx2; omega)
end SemigroupBetti.GenData
