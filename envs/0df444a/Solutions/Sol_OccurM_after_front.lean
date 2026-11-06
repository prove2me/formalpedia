-- Prove2me | solution 1 for OccurM.after_front
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:16:18.020774+00:00
-- url     : https://prove2.me/submissions/207dfea0-e8d1-4697-a544-c6c1d8bb4f44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_OccurM_Prep
import Definitions.Def_OccurM_Arith
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_OccurM_Top
import Theorems.Thm_OccurM_rate_ren
import Theorems.Thm_CountKSatRate_stPaddedW
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_snd
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
import Theorems.Thm_OccurM_one_le_expClauses
import Theorems.Thm_OccurM_steps_le
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_VariableBound_Rename_allOccur_ren
import Theorems.Thm_VariableBound_Rename_isKCNF_ren
import Theorems.Thm_VariableBound_Rename_length_ren
import Theorems.Thm_VariableBound_Rename_numSat_ren
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
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
open OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} {α : ℝ}
namespace OccurM
theorem _root_.solution (h0 : 0 ≤ α) (h1 : α ≤ 1) (hT : GeneralPieces.Tied.TopM S pick (SatM.rPow α))
    (code : ∀ (_ : ℕ) {N : ℕ}, CNF N → List Bool) {front : List Bool → List Bool} (hfront : PolyT front)
    (hcode : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → front (code k φ) = SatM.enc k (ren φ))
    (hlen : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ (code k φ).length) :
    PolyT (fun p : List Bool × U => AM S pick (front p.1, p.2)) ∧ PolyT (fun x => eM S pick (front x)) ∧
    (∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eM S pick (front (code k φ)) ≤ pad.length →
      AM S pick (front (code k φ), pad) = SatK.binary (numOcc φ) (numSatOcc φ)) ∧
    (∃ G : ℕ, ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 2 ≤ φ.length → SatK.IsKCNF k φ → (eM S pick (front (code k φ)) : ℝ) ≤ G * expClauses α k φ.length) ∧
    ∃ (M : TM2ComputableAux Bool Bool) (q C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
      (∀ x : List Bool, Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
        (some ((AM S pick (front x, pad (eM S pick (front x)))).map M.outputAlphabet.invFun)) (q * (x.length + 2 ^ eM S pick (front x) + 1) ^ q))) ∧
      ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length →
        Nonempty (TM2OutputsInTime M.tm ((code k φ).map M.inputAlphabet.invFun)
          (some ((SatK.binary (numOcc φ) (numSatOcc φ)).map M.outputAlphabet.invFun)) (timeClauses α C k φ.length + C * (code k φ).length ^ C)) := by
  have hA : PolyT (fun p : List Bool × U => AM S pick (front p.1, p.2)) := hT.poly_A.comp ((hfront.comp PolyT.id'.fst).prodMk PolyT.id'.snd)
  have he : PolyT (fun x => eM S pick (front x)) := hT.poly_e.comp hfront
  have hc : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → ∀ pad : U, 2 ^ eM S pick (front (code k φ)) ≤ pad.length →
      AM S pick (front (code k φ), pad) = SatK.binary (numOcc φ) (numSatOcc φ) := by
    intro k N φ hk hm hφ pad hp
    rw [hcode k N φ hk hφ] at hp ⊢
    rw [hT.correct k _ (ren φ) hk (by rw [length_ren]; exact hm) (isKCNF_ren φ hφ) (allOccur_ren φ) pad hp, numSat_ren]
  obtain ⟨G, hG⟩ := hT.rate
  have hr : ∀ (k N : ℕ) (φ : CNF N), 1 ≤ k → 2 ≤ φ.length → SatK.IsKCNF k φ → (eM S pick (front (code k φ)) : ℝ) ≤ G * expClauses α k φ.length := by
    intro k N φ hk hm hφ
    rw [hcode k N φ hk hφ]
    exact rate_ren h0 hG φ hk hm hφ
  obtain ⟨M, q, hfin, hM⟩ := CountKSatRate.stPaddedW (fun x => eM S pick (front x)) (fun p => AM S pick (front p.1, p.2)) he hA
  refine ⟨hA, he, hc, ⟨G, hr⟩, M, q, stepsC q G, hfin, hM, fun k N φ hk hφ hm => ?_⟩
  have hx := hM (code k φ)
  simp only [hc k N φ hk (by omega) hφ (pad (eM S pick (front (code k φ)))) (by simp [pad])] at hx
  obtain ⟨ev⟩ := hx
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (steps_le q G (hr k N φ hk hm hφ) (one_le_expClauses h0 h1 hk hm) (hlen k N φ))⟩⟩
end OccurM
