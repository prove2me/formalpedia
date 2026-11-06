-- Prove2me | solution 1 for OccurM.rate_ren
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:58:06.646159+00:00
-- url     : https://prove2.me/submissions/de5306f3-8953-4e5f-aba2-cbaf92661240

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_OccurM_shift_le
import Theorems.Thm_VariableBound_Rename_allOccur_ren
import Theorems.Thm_VariableBound_Rename_isKCNF_ren
import Theorems.Thm_VariableBound_Rename_length_ren
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur VariableBound.Rename
open Sat3 (CNF)
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {pick : U → U × Idx} {α : ℝ}
namespace OccurM
theorem _root_.solution (h0 : 0 ≤ α) {G : ℕ}
    (hG : ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
      (eM S pick (SatM.enc k φ) : ℝ) ≤ G * ((k : ℝ) * φ.length * SatM.rPow α φ.length))
    {k N : ℕ} (φ : CNF N) (hk : 1 ≤ k) (hm : 2 ≤ φ.length) (hφ : SatK.IsKCNF k φ) :
    (eM S pick (SatM.enc k (ren φ)) : ℝ) ≤ G * expClauses α k φ.length := by
  have h := hG k _ (ren φ) hk (by rw [length_ren]; omega) (isKCNF_ren φ hφ) (allOccur_ren φ)
  rw [length_ren] at h
  exact h.trans (mul_le_mul_of_nonneg_left (shift_le h0 k hm) (Nat.cast_nonneg G))
end OccurM
