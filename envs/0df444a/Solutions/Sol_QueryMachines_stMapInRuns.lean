-- Prove2me | solution 1 for QueryMachines.stMapInRuns
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:33:07.278742+00:00
-- url     : https://prove2.me/submissions/466720f8-6d25-40a7-819b-44b93352330f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
set_option autoImplicit false
section
section
open QueryMachines
open Groundwork Finset QueryMachine

theorem solution : StMapInRuns := by
  intro Q A α β γ g M O a own S L c h
  unfold QueryMachine.Runs at h ⊢
  change (QueryMachine.mapIn g M).Reaches O S c (M.init (g a)) own L
  generalize M.init (g a) = s at h ⊢
  induction h with
  | halt hout hs =>
      exact .halt hout hs
  | step hout hask hs _ ih =>
      exact .step hout hask hs ih
  | query hout hask hO hs _ ih =>
      exact .query hout hask hO hs ih
