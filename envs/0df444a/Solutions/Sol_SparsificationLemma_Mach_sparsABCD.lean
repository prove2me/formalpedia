-- Prove2me | solution 1 for SparsificationLemma.Mach.sparsABCD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:10:37.877438+00:00
-- url     : https://prove2.me/submissions/cd6971f1-e628-4d21-aa66-8402b2906bd2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_SparsificationLemma_Geo_S
import Definitions.Def_SparsificationLemma_Mach_Len
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Mach_Full
import Theorems.Thm_SparsificationLemma_Mach_sparsABCD_of
import Theorems.Thm_SparsificationLemma_Geo_stThmS


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
namespace SparsificationLemma.Mach
theorem _root_.solution (hP : Prints) : SparsABCD := sparsABCD_of stThmS hP
end SparsificationLemma.Mach
