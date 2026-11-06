-- Prove2me | solution 1 for PairsToBound.exhaustiveMachineExists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:27.394238+00:00
-- url     : https://prove2.me/submissions/eaeedf19-5a11-4451-b722-2ecff22ccf75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Exhaust
import Theorems.Thm_PairsToBound_triesAllWithin_of_computes
import Theorems.Thm_PairsToBound_exhaust_polyT
import Theorems.Thm_ClauseBound_Alg_Decode_stCertDecM
import Theorems.Thm_CountKSatRate_stPaddedW
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg Wrap MainTheoremForms
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution : ExhaustiveMachineExists := by
  obtain ⟨Mb, q, hfin, hM⟩ := stPaddedW (fun x => (fmlOf x).1.length) exhaust (PolyT.length Decode.stCertDecM.2.fst) exhaust_polyT
  exact ⟨Mb, 8 * q, q, hfin, triesAllWithin_of_computes hM, hM⟩
end PairsToBound
