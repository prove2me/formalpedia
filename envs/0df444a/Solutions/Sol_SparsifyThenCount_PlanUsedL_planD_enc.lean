-- Prove2me | solution 1 for SparsifyThenCount.PlanUsedL.planD_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:51:38.70534+00:00
-- url     : https://prove2.me/submissions/58e9d945-9290-4851-96e7-04ac0980a309

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_PlanUsedDefs
import Definitions.Def_SparsifyThenCount_Main
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_ClauseBound_Alg_Decode
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SparsifyThenCount_PlanUsed
import Theorems.Thm_ClauseBound_Alg_Decode_stDecM
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_CertNet_nU
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] PaddedDescent.F.CertNet.nU



set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide Filter
open SparsifyThenCount.PlanUsedL
variable {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U)
namespace SparsifyThenCount.PlanUsedL
theorem _root_.solution {k n : ℕ} (φ : Sat3.CNF n) (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) :
    planD S pick slU (SatM.enc k φ) = planAtD S k n (pick (root17 n)).2 (slU (pick (root17 n)).1).length := by
  obtain ⟨hdk, hdf⟩ := Decode.stDecM k n φ hk hφ.1
  have hkU : kU (SatM.enc k φ) = k := by rw [kU, hdk, List.length_replicate]
  have hnU : nU (SatM.enc k φ) = n := by rw [nU, hdf, List.length_replicate]
  rw [planD, idxU, precU, hkU, hnU]
end SparsifyThenCount.PlanUsedL
