-- Prove2me | solution 1 for VariableBound.Search.fold_stepD_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:54:35.911245+00:00
-- url     : https://prove2.me/submissions/c1a13174-fd32-455e-a9cf-543315482345

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Search_Cert
import Theorems.Thm_VariableBound_Search_stepD_cases

set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
omit [Enc α]
namespace VariableBound.Search
theorem _root_.solution (key : List ℕ → ℤ) (S : List (List ℕ)) : ∀ (r : List (List ℕ)) (c : Option (List ℕ × ℤ)), (∀ l ∈ r, l ∈ S) →
    (c = none ∨ ∃ l ∈ S, c = some (l, key l)) → (r.foldl (stepD key) c = none ∨ ∃ l ∈ S, r.foldl (stepD key) c = some (l, key l)) := by
  intro r
  induction r with
  | nil => intro c _ h; exact h
  | cons a t ih =>
    intro c hr hc
    rw [List.foldl_cons]
    refine ih _ (fun l hl => hr l (List.mem_cons_of_mem _ hl)) ?_
    rcases stepD_cases key c a with h | h
    · exact Or.inr ⟨a, hr a List.mem_cons_self, h⟩
    · rw [h]; exact hc
end VariableBound.Search
