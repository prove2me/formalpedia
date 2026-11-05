-- Prove2me | solution 1 for Sat3.eq_of_header
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:43:52.381614+00:00
-- url     : https://prove2.me/submissions/cdd5e55c-2648-40cd-ad2c-a6f22e4e238c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_StepMachines_Math_Formula

set_option autoImplicit false
section
open Sat3
namespace Sat3
theorem _root_.solution : ∀ {n m : ℕ} {l l' : List Bool},
    List.replicate n true ++ false :: l = List.replicate m true ++ false :: l' → n = m ∧ l = l'
  | 0, 0, _, _, h => by simpa using h
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | n + 1, m + 1, _, _, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := solution h
    exact ⟨rfl, rfl⟩
end Sat3
