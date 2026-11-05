-- Prove2me | solution 1 for PaddedDescent.Col.exists_goodG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:21:41.096162+00:00
-- url     : https://prove2.me/submissions/e7195d4d-297a-42ad-8902-bfe7835ba9c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Col_Colouring
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_Col_Good
import Theorems.Thm_PaddedDescent_Col_goodG_iff
import Theorems.Thm_Groundwork_Network_merge_c
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
import Theorems.Thm_PaddedDescent_Col_exists_colouring_cap_nat
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.Col
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F Finset
variable {C : Type}
variable {K g : ℕ} (Np : PNet C) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
namespace PaddedDescent.Col
theorem _root_.solution {M D m β : ℕ} (hK : 1 ≤ K) (hN : Np.Presents c N t S) (hM0 : 0 < M) (hD : 1 ≤ D)
    (hM : ∀ a b, a ≠ b → N.c a b ≤ M) (h1 : 4 * D ^ 2 * m * K ≤ g) (h2 : (g + 2) * K < 2 ^ m)
    (hβ : D * N.U + 3 * g ^ 2 * M ≤ D * K ^ 2 * β) : ∃ x < K ^ g, goodG K g Np β (c, x) = true := by
  have hK0 : 0 < K := hK
  obtain ⟨χ, a1, a2⟩ := exists_colouring_cap_nat hK (fun a b => if a = b then 0 else N.c a b) M D m hM0 hD
    (fun a b => by
      by_cases e : a = b
      · simp [e]
      · simpa [e] using hM a b e) h1 h2
  have hχ : chi hK0 (finFunctionFinEquiv χ).val = χ := by
    funext a
    have := congrFun (finFunctionFinEquiv.symm_apply_apply χ) a
    rw [← this]
    rfl
  refine ⟨(finFunctionFinEquiv χ).val, (finFunctionFinEquiv χ).2, (goodG_iff Np hK0 hN β _).2 ?_⟩
  rw [hχ]
  refine ⟨a1, fun G G' hne => ?_⟩
  rw [Network.merge_c]
  have e1 : ∑ a with χ a = G, ∑ b with χ b = G', (if a = b then 0 else N.c a b)
      = ∑ a with χ a = G, ∑ b with χ b = G', N.c a b := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have hab : a ≠ b := fun e => hne (by rw [← (Finset.mem_filter.1 ha).2, ← (Finset.mem_filter.1 hb).2, e])
    rw [if_neg hab]
  have e2 : ∑ a, ∑ b, (if a = b then 0 else N.c a b) = N.U := by
    rw [Network.U]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_erase (univ : Finset (Fin g)) (a := a) (by simp)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [if_neg (Finset.ne_of_mem_erase hb).symm]
  have a3 := a2 G G'
  rw [e1, e2] at a3
  have hpos : 0 < D * K ^ 2 := by positivity
  exact Nat.le_of_mul_le_mul_left (a3.trans hβ) hpos
end PaddedDescent.Col
