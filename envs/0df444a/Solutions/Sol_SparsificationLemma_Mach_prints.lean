-- Prove2me | solution 1 for SparsificationLemma.Mach.prints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:55:00.645213+00:00
-- url     : https://prove2.me/submissions/543d8c6a-44c8-4ab4-8670-9d0f90384a38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Mach_Cert
import Definitions.Def_SparsificationLemma_Mach_Len
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Definitions.Def_SparsificationLemma_Mach_Main
import Theorems.Thm_SparsificationLemma_Mach_time_le
import Theorems.Thm_ClauseBound_Alg_End_time_le
import Theorems.Thm_CountKSatRate_stPaddedW
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Mach_BL_eq
import Theorems.Thm_SparsificationLemma_Mach_Cert_polyT_BL
import Theorems.Thm_SparsificationLemma_Mach_Cert_polyT_eL
import Theorems.Thm_SparsificationLemma_Mach_eL_encIn
import Theorems.Thm_SparsificationLemma_Mach_length_encIn
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution : Prints := by
  obtain ⟨M, q, hfin, hM⟩ := stPaddedW eL BL Cert.polyT_eL Cert.polyT_BL
  refine ⟨M, q * 4097 ^ q + 4 * q, hfin, fun k n s φ hk hs hφ hnil => ?_⟩
  obtain ⟨ev⟩ := hM (encIn s k φ)
  rw [BL_eq k n s φ hk hs hφ hnil, eL_encIn s k n φ hk hφ.1] at ev
  have hN : 1 ≤ (encIn s k φ).length := by rw [length_encIn]; omega
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (time_le q (n / 2 ^ s) k hN)⟩⟩
end SparsificationLemma.Mach
