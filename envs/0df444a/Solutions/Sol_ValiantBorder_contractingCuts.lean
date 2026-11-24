-- Prove2me | solution 1 for ValiantBorder.contractingCuts
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:06:14.320611+00:00
-- url     : https://prove2.me/submissions/e0774802-8e97-4f8f-be79-b13ddaba8161

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_contractingLocalCuts
import Theorems.Thm_ValiantBorder_amplifyLocalCuts
/-! Based on Claude (Anthropic), *VP ≠ VNP over every field*, Theorems onecut and cut,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp .
This arrangement refactors the single-cut hypothesis from its quantitative amplification.
The upstream Lean source is copyright 2026 Anthropic, PBC and released under Apache 2.0,
https://www.apache.org/licenses/LICENSE-2.0. -/
theorem solution {K : Type} [Field K] (hK : Paper.Contracting K) :
    ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A) (θ : List Bool → A) (h C₀ v₀ : ℕ),
      (Function.support θ).Finite ∧ 17 ≤ h ∧ NS1.CutHyp θ (16 * h) C₀ v₀ := by
  obtain ⟨A,hA,θ,hθ,hc⟩ := ValiantBorder.contractingLocalCuts hK
  obtain ⟨h,C₀,v₀,hh,hcut⟩ := ValiantBorder.amplifyLocalCuts hc
  exact ⟨A,hA,θ,h,C₀,v₀,hθ,hh,hcut⟩
