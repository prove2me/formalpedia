-- Prove2me | solution 1 for Sat3.inRateTM_of_mulForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:41:28.404945+00:00
-- url     : https://prove2.me/submissions/65c31bb6-cbaf-4981-8f5c-3aca6a1e5351

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
import Theorems.Thm_Sat3_le_rateBound_of_mul_le
import Theorems.Thm_Sat3_log2_log2_le_sOf
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
theorem _root_.solution (M : TM2ComputableAux Bool Bool) (hfin : ∀ k, Finite (M.tm.Γ k)) (A C₁ : ℕ) (t e : ℕ → ℕ)
    (h : DecidesTM M t) (ht : ∀ n, t n ≤ A * 2 ^ e n)
    (he : ∀ n, e n * 2 ^ PaddedDescent.sOf n ≤ C₁ * (n + 2 ^ PaddedDescent.sOf n)) : InRateTM (3 / 19) := by
  refine ⟨M, A * 2 ^ C₁ + C₁ * 2 ^ 146, hfin, h.mono fun n => (ht n).trans ?_⟩
  have := le_rateBound_of_mul_le (p := 3) (A := A) (by norm_num : 0 < 19) (log2_log2_le_sOf n) (he n)
  exact_mod_cast this
end Sat3
