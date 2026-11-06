-- Prove2me | solution 1 for ThmCount.numSat_pad4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:06:30.3412+00:00
-- url     : https://prove2.me/submissions/7c4188bf-1780-4e01-80bc-f5e291cd6699

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic
import Definitions.Def_ThmCount_FrontEnd
import Theorems.Thm_ThmCount_holds_pad4

set_option autoImplicit false
section
section
section
open ThmCount
open Groundwork Groundwork.Decode
namespace ThmCount
theorem _root_.solution {n : ℕ} (φ : Sat3.CNF n) : SatK.numSat (Wrap.pad4 φ) = SatK.numSat φ := by
  unfold SatK.numSat
  symm
  refine Finset.card_bij (fun a _ => Fin.append a fun _ : Fin 4 => true) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, (holds_pad4 φ _).2 ⟨fun C hC => ?_, fun j => by rw [Fin.append_right]⟩⟩
    obtain ⟨l, hl, e⟩ := ha.2 C hC
    exact ⟨l, hl, by rw [Fin.append_left]; exact e⟩
  · intro a _ a' _ h
    funext i
    have := congrFun h (Fin.castAdd 4 i)
    rwa [Fin.append_left, Fin.append_left] at this
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨h1, h2⟩ := (holds_pad4 φ b).1 hb.2
    refine ⟨fun i => b (Fin.castAdd 4 i), Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩, ?_⟩
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · rw [Fin.append_left]
    · rw [Fin.append_right, h2 j]
end ThmCount
