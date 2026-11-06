-- Prove2me | solution 1 for SparsificationLemma.Mach.lemSparsification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:02:01.369132+00:00
-- url     : https://prove2.me/submissions/c66fd69c-005d-49ed-9bf5-75b174938075

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Mach_Full
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Mach_LemSparsification
import Theorems.Thm_SparsificationLemma_Mach_lemSparsification_of
import Theorems.Thm_SparsificationLemma_Mach_sparsABCD


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution (hP : Prints) : LemSparsification := lemSparsification_of (sparsABCD hP)
end SparsificationLemma.Mach
