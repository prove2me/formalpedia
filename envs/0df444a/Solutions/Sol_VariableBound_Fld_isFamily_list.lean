-- Prove2me | solution 1 for VariableBound.Fld.isFamily_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:23:08.157839+00:00
-- url     : https://prove2.me/submissions/a8721a94-12a9-4741-b993-039ee6a92e7c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Definitions.Def_VariableBound_Field_Transfer
import Theorems.Thm_VariableBound_Fld_isFamily_comap
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
open VariableBound VariableBound.Fld
open Groundwork Finset
namespace VariableBound.Fld
theorem _root_.solution {m v : ℕ} {ι U : Type} (Ω : Finset ι) (Γ : ι → Finset (Fin m)) (L : List U) (D : U → ι) (G : U → List ℕ)
    (hL : L.Nodup) (hD : ∀ u ∈ L, ∀ u' ∈ L, D u = D u' → u = u') (hΩ : ∀ w, w ∈ Ω ↔ ∃ u ∈ L, D u = w)
    (hG : ∀ u ∈ L, setD m (G u) = Γ (D u)) (h : AppVariables.IsFamily v Ω Γ) :
    #Ω = (L.map G).length ∧ AppVariables.IsFamily v (univ : Finset (Fin (L.map G).length)) fun i => setD m ((L.map G).get i) := by
  have hlen : (L.map G).length = L.length := List.length_map G
  let φ : Fin (L.map G).length ↪ ι := ⟨fun i => D (L.get (i.cast hlen)), fun i j hij => by
    have := hD _ (List.get_mem L _) _ (List.get_mem L _) hij
    have := (List.Nodup.get_inj_iff hL).1 this
    exact Fin.cast_injective hlen this⟩
  have hmap : Ω = (univ : Finset (Fin (L.map G).length)).map φ := by
    ext w
    rw [hΩ, Finset.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hu
      exact ⟨i.cast hlen.symm, Finset.mem_univ _, rfl⟩
    · rintro ⟨i, _, rfl⟩
      exact ⟨_, List.get_mem L _, rfl⟩
  refine ⟨by rw [hmap, Finset.card_map, Finset.card_univ, Fintype.card_fin], ?_⟩
  have key := isFamily_comap h φ univ hmap
  have e : (fun i : Fin (L.map G).length => setD m ((L.map G).get i)) = fun i => Γ (φ i) := by
    funext i
    have : (L.map G).get i = G (L.get (i.cast hlen)) := by simp
    rw [this, hG _ (List.get_mem L _)]
    rfl
  rw [e]
  exact key
end VariableBound.Fld
