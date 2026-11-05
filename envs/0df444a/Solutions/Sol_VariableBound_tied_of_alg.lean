-- Prove2me | solution 1 for VariableBound.tied_of_alg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:38:28.196202+00:00
-- url     : https://prove2.me/submissions/da0472d4-2741-4d08-ac20-6891be470280

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_TiedDefs
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_VariableBound_Printed_Tied
import Theorems.Thm_VariableBound_mul_pow_mono
import Theorems.Thm_ClauseBound_Both_End_bound_mono
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
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
import Theorems.Thm_Groundwork_TM_update_withIO
import Theorems.Thm_Groundwork_Unary_comp
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
import Theorems.Thm_UniformInK_End_boundBothK_of_ge
import Theorems.Thm_UniformInK_End_boundBothK_of_le
import Theorems.Thm_UniformInK_End_boundNK_mono
import Theorems.Thm_UniformInK_End_one_le_length
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
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
attribute [local simp] Groundwork.TM.update_withIO
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
open VariableBound
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK UniformInK.End VariableBound.Decide
namespace VariableBound
theorem _root_.solution (hP : StPaddedW) {rn rm : ℕ → ℝ} {A : List Bool × U → List Bool} {e : List Bool → ℕ} (h : Alg rn rm A e) {post : List Bool → List Bool} (hpost : PolyT post)
    (hrn0 : ∀ n, 0 ≤ rn n) (hrm0 : ∀ m, 0 ≤ rm m) : TiedOut A e post rn rm := by
  obtain ⟨N, q, hfin, hN⟩ := hP e (fun p => post (A p)) h.polyE (hpost.comp h.polyA)
  obtain ⟨D, hD⟩ := h.timeN q
  obtain ⟨D', hD'⟩ := h.timeM q
  have hrun : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → SatK.IsKCNF k φ → ∀ t : ℕ, q * ((SatM.enc k φ).length + 2 ^ e (SatM.enc k φ) + 1) ^ q ≤ t →
      Nonempty (TM2OutputsInTime N.tm ((SatM.enc k φ).map N.inputAlphabet.invFun) (some ((post (SatK.binary n (SatK.numSat φ))).map N.outputAlphabet.invFun)) t) := by
    intro k n φ hk hφ t ht
    have hx := hN (SatM.enc k φ)
    rw [h.correct k n φ hk hφ (pad (e (SatM.enc k φ))) (by simp [pad])] at hx
    obtain ⟨ev⟩ := hx
    exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ht⟩⟩
  have hn : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
      q * ((SatM.enc k φ).length + 2 ^ e (SatM.enc k φ) + 1) ^ q ≤ SatM.boundNK rn (max q (max D D')) k n := fun k n φ hk hn1 hφ =>
    (hD k n φ hk hn1 hφ).trans (boundNK_mono ((le_max_left _ _).trans (le_max_right _ _)) k n (hrn0 n))
  have hm : ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
      q * ((SatM.enc k φ).length + 2 ^ e (SatM.enc k φ) + 1) ^ q ≤ SatM.bound rm (max q (max D D')) k φ.length := fun k n φ hk hm1 hφ ho =>
    (hD' k n φ hk hm1 hφ ho).trans (bound_mono ((le_max_right _ _).trans (le_max_right _ _)) k φ.length (hrm0 _))
  refine ⟨N, max q (max D D'), hfin, fun x => ?_, fun k n φ hk hn1 hφ => hrun k n φ hk hφ _ (hn k n φ hk hn1 hφ), fun k n φ hk hm1 hφ ho => hrun k n φ hk hφ _ (hm k n φ hk hm1 hφ ho),
    fun k n φ hk hn1 hφ ho => hrun k n φ hk hφ _ ?_⟩
  · obtain ⟨ev⟩ := hN x
    exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (mul_pow_mono (le_max_left _ _) (Nat.le_add_left 1 _))⟩⟩
  · rcases le_total ((k : ℝ) ^ 2 * n * rn n) ((k : ℝ) * φ.length * rm φ.length) with hle | hle
    · rw [boundBothK_of_le hle]
      exact hn k n φ hk hn1 hφ
    · rw [boundBothK_of_ge hle]
      exact hm k n φ hk (one_le_length hn1 ho) hφ ho
end VariableBound
