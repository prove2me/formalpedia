-- Prove2me | solution 1 for WidthK.ProgMain.G_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:53:58.540051+00:00
-- url     : https://prove2.me/submissions/4ff4d2e9-a696-4ce7-886a-7ad6c83e6cd9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
import Theorems.Thm_WidthK_ProgMain_step_spec

set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
namespace WidthK.ProgMain
theorem _root_.solution (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) (ψ : PFml) (s : PFml) (p t : ℕ) (l h : PFml)
    (hG : G Node ψ s p t) (hst : stepK θ k s = some (l, h)) : G Node ψ l (p + 1) t ∧ G Node ψ h (p + 1) (t + q) := by
  obtain ⟨j, H, hrule, hl, hh, hnl, hnh⟩ := step_spec hI hR hG hst
  obtain ⟨h1, h2⟩ := hI.step _ _ _ _ _ _ hG.2 hrule
  exact ⟨⟨hnl, hl ▸ h1⟩, ⟨hnh, hh ▸ h2⟩⟩
end WidthK.ProgMain
