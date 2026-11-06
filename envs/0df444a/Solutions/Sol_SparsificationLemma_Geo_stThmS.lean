-- Prove2me | solution 1 for SparsificationLemma.Geo.stThmS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:46:36.260019+00:00
-- url     : https://prove2.me/submissions/4fcdf2dc-6a0b-4ec6-a83b-12abe7640173

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_SparsificationLemma_Geo_S
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_SparsificationLemma_Geo_stThmTau
import Theorems.Thm_UniformInK_Leaves_bsumU_tauOf
import Theorems.Thm_UniformInK_Leaves_tauOf_worksU
import Theorems.Thm_UniformInK_stParU
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Geo
open Finset Groundwork Groundwork.Sparsify CountKSat UniformInK PaddedDescent
namespace SparsificationLemma.Geo
theorem _root_.solution : StThmS := by
  intro k n s φ hk hs hφ
  obtain ⟨t1, t2, t3, t4, t5⟩ := stThmTau k n (tauOf s) (1 / 2 ^ s) φ hk ((stParU k s hk).2 hs).2 (Leaves.tauOf_worksU hk hs) hφ
  have e : (1 : ℝ) / 2 ^ s * (n : ℝ) = (n : ℝ) / 2 ^ s := by ring
  rw [e] at t3
  refine ⟨t1, t2, t3, ?_, t4, fun Φ hΦ v => ?_⟩
  · have h2 : n < 2 ^ s * (n / 2 ^ s + 1) := Nat.lt_mul_div_succ n (by positivity)
    have h3 : (n : ℝ) ≤ (2 : ℝ) ^ s * ((n / 2 ^ s + 1 : ℕ) : ℝ) := by exact_mod_cast h2.le
    have h4 : (n : ℝ) / 2 ^ s ≤ ((n / 2 ^ s + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h5 : ((outTau k n (tauOf s) φ).length : ℝ) ≤ ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by
      calc ((outTau k n (tauOf s) φ).length : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 ^ s) := t3
        _ ≤ (2 : ℝ) ^ (((n / 2 ^ s + 1 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
        _ = ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
    exact_mod_cast h5
  · have := t5 Φ hΦ v
    rwa [← bsumU, Leaves.bsumU_tauOf] at this
end SparsificationLemma.Geo
