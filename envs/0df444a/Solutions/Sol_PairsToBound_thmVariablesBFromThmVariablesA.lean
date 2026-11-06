-- Prove2me | solution 1 for PairsToBound.thmVariablesBFromThmVariablesA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:57:53.557188+00:00
-- url     : https://prove2.me/submissions/bd4533dd-ad86-4af1-afe8-2ad50b21c769

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_PairsToBound_Pairs
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_PairsToBound_Width
import Definitions.Def_PairsToBound_FrontEnd
import Definitions.Def_PairsToBound_Exhaust
import Definitions.Def_TwoMachines_Main
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_PairsToBound_Main
import Theorems.Thm_PairsToBound_everyChoiceMeetsThmVariablesB
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_PairsToBound_exhaustiveMachineExists
import Theorems.Thm_PairsToBound_frontEndAndTestExist
import Theorems.Thm_TwoMachines_everyTwoMachinesCanBeChosenBetween
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution : ThmVariablesBFromThmVariablesA := by
  intro Idx _ S e C₀ Q a he M C' hfin hM
  refine ⟨?_, everyChoiceMeetsThmVariablesB Idx S e C₀ Q a he M C' hM⟩
  obtain ⟨Mb, c, qb, hfb, hMb, hcomp⟩ := exhaustiveMachineExists
  obtain ⟨⟨pre, hpp, hpre⟩, hT⟩ := frontEndAndTestExist
  obtain ⟨test, htp, htest⟩ := hT (S.K (Q.idx 0))
  obtain ⟨K₁, K₂, N, q₀, q, hfN, hH, hCh⟩ := everyTwoMachinesCanBeChosenBetween M Mb hfin hfb test pre id id id htp hpp PolyT.id' PolyT.id' PolyT.id'
  exact ⟨Mb, c, qb, pre, test, K₁, K₂, N, q₀, q, hfb, hMb, hcomp, hpp, hpre, htp, htest, hfN, hH, hCh⟩
end PairsToBound
