-- Prove2me | solution 1 for Value.stSumOut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:54:55.676668+00:00
-- url     : https://prove2.me/submissions/ded4e584-3a4c-4b42-a62d-4cdd76261ae5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Sums
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_sum_tuples_prod
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks
variable {g K : ℕ}
namespace Value
theorem _root_.solution : StSumOut := by
  intro g K P B N hN χ z hz
  rw [Fintype.mem_piFinset] at hz
  have hs : (pairs (Fin g)).filter (fun p => χ p.1 ≠ χ p.2) = univ.filter (Across χ) := by
    rw [pairs, Finset.filter_filter]
  unfold jointTerm blockStrings
  rw [← Finset.mul_sum, hs, sum_tuples_prod (Across χ) (fun p => words (N.c p.1 p.2)) [] fun p θ => N.f p.1 p.2 (z p.1) θ * N.f p.2 p.1 (z p.2) θ, ← hs, mul_assoc]
  congr 1
  rw [← Finset.prod_filter_mul_prod_filter_not (pairs (Fin g)) fun p => χ p.1 = χ p.2]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hlt : p.1 < p.2 := (mem_filter.1 (mem_filter.1 hp).1).2
  exact (hN.fact p.1 p.2 hlt.ne (z p.1) (hz p.1) (z p.2) (hz p.2)).symm
end Value
