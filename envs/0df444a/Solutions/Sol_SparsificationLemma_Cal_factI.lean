-- Prove2me | solution 1 for SparsificationLemma.Cal.factI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:40:03.401977+00:00
-- url     : https://prove2.me/submissions/a42f4eb7-66a9-49dd-b3bc-ee32d1a6e287

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Facts
import Theorems.Thm_SparsificationLemma_Cal_gen

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
namespace SparsificationLemma.Cal
theorem _root_.solution : FactI := fun _ _ _ _ hα hk hψ => (gen hα hk hψ).1
end SparsificationLemma.Cal
