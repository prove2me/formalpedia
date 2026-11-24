-- Prove2me | solution 1 for ValiantBorder.contractingAcceleratorObstruction
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:00:28.575823+00:00
-- url     : https://prove2.me/submissions/12ab6493-c7dc-4129-8f49-5691534f9b48

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Theorems.Thm_ValiantBorder_contractingCuts
import Theorems.Thm_ValiantBorder_cutExcludesApproximateAccelerators
/-! Source: Claude (Anthropic), *VP ≠ VNP over every field* (2026),
`anthropics/formal-math` commit 11b6c7e3c927df2658f513b6b68ea7f8929c62c5.
Adapted with attribution under the Apache-2.0 license. -/
theorem solution {K : Type} [Field K] (hK : Paper.Contracting K) :
    ∃ (A : Subring K) (θ : List Bool → A) (h : ℕ), (Function.support θ).Finite ∧ 17 ≤ h ∧
      ∃ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∀ a, NS1.lg v ^ (C * a) ≤ v →
        ¬ NS1.HasAccA θ K (16 * h) v (v ^ a) := by
  obtain ⟨A, hA, θ, h, C₀, v₀, hθ, hh, hcut⟩ := ValiantBorder.contractingCuts hK
  letI := hA
  obtain ⟨C,v₁,hn⟩ := ValiantBorder.cutExcludesApproximateAccelerators hh hcut
  exact ⟨A, θ, h, hθ, hh, C, v₁, fun v hv a ha => hn v hv a ha K⟩
