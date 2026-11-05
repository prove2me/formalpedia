-- Prove2me | solution 1 for PaddedDescent.F.RebalF.presents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:50:41.287197+00:00
-- url     : https://prove2.me/submissions/3d72b410-43ba-4f50-933d-032292055994

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_PaddedDescent_F_RebalF_freeM_runs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
namespace PaddedDescent.F.RebalF
theorem _root_.solution {C : Type} (F : FNet C) (c : C) {g : ℕ} (N : Network (Fin g) (List Bool) (List Bool))
    (hS : ∀ a : Fin g, N.S a = words (F.n c a))
    (hc : ∀ a b : Fin g, a ≠ b → N.c a b = F.cap c a b)
    (hl : ∀ a b : Fin g, a ≠ b → N.lab a b = words (F.cap c a b))
    (hW : ∀ (a : Fin g) (z : List Bool), z.length = F.n c a → F.W (c, (a.val, z)) = N.W a z)
    (hf : ∀ (a b : Fin g) (z θ : List Bool), a ≠ b → z.length = F.n c a → θ.length = F.cap c a b →
      F.f (c, ((a.val, b.val), (z, θ))) = N.f a b z θ) :
    F.toP.Presents c N 0 0 where
  S_eq := hS
  c_eq := hc
  lab_eq := hl
  W_runs a z hz := by rw [← hW a z hz]; exact freeM_runs _ _
  f_runs a b z θ hab hz hθ := by rw [← hf a b z θ hab hz hθ]; exact freeM_runs _ _
end PaddedDescent.F.RebalF
