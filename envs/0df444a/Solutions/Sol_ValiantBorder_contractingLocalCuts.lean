-- Prove2me | solution 1 for ValiantBorder.contractingLocalCuts
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:08:06.049699+00:00
-- url     : https://prove2.me/submissions/9f7e7895-0d08-49bc-9a83-1e6539b19028

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_contractingLaws
import Theorems.Thm_ValiantBorder_lawsToLocalCuts
/-! Based on Claude (Anthropic), *VP ≠ VNP over every field*, Theorems onecut and cut,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp .
This arrangement refactors the single-cut hypothesis from its quantitative amplification.
The upstream Lean source is copyright 2026 Anthropic, PBC and released under Apache 2.0,
https://www.apache.org/licenses/LICENSE-2.0. -/
theorem solution {K : Type} [Field K] (hK : Paper.Contracting K) :
    ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A) (θ : List Bool → A),
      (Function.support θ).Finite ∧ NS1.LocalCuts θ := by
  obtain ⟨h, hne, h3, A, hA, VL, hgain, _⟩ := ValiantBorder.contractingLaws hK
  obtain ⟨θ, hθ, hc⟩ := ValiantBorder.lawsToLocalCuts VL h3 hgain
  exact ⟨A, hA, θ, hθ, hc⟩
