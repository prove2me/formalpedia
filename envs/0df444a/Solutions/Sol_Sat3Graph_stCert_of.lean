-- Prove2me | solution 1 for Sat3Graph.stCert_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:30:18.957968+00:00
-- url     : https://prove2.me/submissions/795f35b8-c661-4667-94db-fa4e5b62dd68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SizeCircuit_SizedCert
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Walk
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Cert
import Theorems.Thm_Sat3Graph_askSized_polyTimeSteps
import Theorems.Thm_Sat3Graph_readC_polyT_alone
import Theorems.Thm_Eight_Width_widthP_polyT
import Theorems.Thm_GraphProblems_readF_polyT
import Theorems.Thm_GraphProblems_stCertDom
import Theorems.Thm_GraphProblems_stCertRead
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.comp



set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit Complement SplitSat
namespace Sat3Graph
theorem _root_.solution (hRC : Complement.StReadersCert) (hI : Complement.StIndepAlone) : StCert := by
  intro gates hC D hD
  obtain ⟨hA⟩ := askSized_polyTimeSteps hC hD
  obtain ⟨hD'⟩ := hD
  refine ⟨⟨IsPolyT.mapIn (M := askSized gates D) (readF_polyT stCertRead hI.1)⟩, ⟨IsPolyT.mapIn (M := askSized gates D) hRC.1⟩,
    ⟨IsPolyT.mapIn (M := askSized gates D) hRC.2⟩, fun w => ?_, fun k => ?_⟩
  · have := IsPolyT.mapIn (M := askSized gates D) stCertDom.2.2
    have := IsPolyT.walk (T := Stepped.mapIn leafD (askSized gates D)) (step := stepD w) (root := rootD) (stCertDom.1 w) stCertDom.2.1
    exact ⟨IsPolyT.mapIn (M := Stepped.walk (stepD w) rootD (Stepped.mapIn leafD (askSized gates D))) stCertRead.2⟩
  · exact ⟨IsPolyT.mapIn (M := D) (f := fun x => widthP (readC k x)) (PolyT.comp widthP_polyT (readC_polyT_alone k))⟩
end Sat3Graph
