-- Prove2me | solution 1 for Variance.stCovDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:30:42.008198+00:00
-- url     : https://prove2.me/submissions/723836a2-c1f6-48de-a0e3-6ca4f23d9de5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Cov
import Theorems.Thm_Eight_SecNetworks_cov_disjoint


set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks
namespace Variance
theorem _root_.solution : StCovDisjoint := by
  intro g K γ γ' p hp q hq hm
  have hp' : p.1 ≠ p.2 := (mem_filter.1 hp).2
  have hq' : q.1 ≠ q.2 := (mem_filter.1 hq).2
  obtain ⟨h1, h2, h3, h4⟩ : q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.2 ≠ p.1 ∧ q.2 ≠ p.2 := by
    refine ⟨fun h => hm (.inl h), fun h => hm (.inr (.inl h)), fun h => hm (.inr (.inr (.inl h))), fun h => hm (.inr (.inr (.inr h)))⟩
  have h := cov_disjoint hp' h1.symm h3.symm h2.symm h4.symm hq' γ γ'
  unfold cov
  have h' : ((#{χ : Fin g → Fin K | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')} : ℕ) : ℤ) * (K : ℤ) ^ 4 = (K : ℤ) ^ g := by exact_mod_cast h
  linarith
end Variance
