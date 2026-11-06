-- Prove2me | solution 1 for VariableBound.Count.evF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:00:40.442346+00:00
-- url     : https://prove2.me/submissions/f15ad45a-adea-4851-923e-ebc395948843

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct
import Theorems.Thm_VariableBound_Count_card_Vof
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace VariableBound.Count
theorem _root_.solution (hEv : Net.StEvXF) (hNP : Net.StNPrMax) (hProd : AppVariables.ProductStmt) {ok : Idx → Prop} (hC : S.Correct ok) {k : ℕ} {pad : U} {i : Idx} {n Δ nb M : ℕ} {ψ : Fml}
    {L : List (List ℕ)} (hok : ok i) (hK : 2 ≤ S.K i) (hfit : FitsD S k i n Δ pad.length) (hF : Fit k n Δ nb M (ψ, L)) (h1 : beta n ψ.length nb - 1 + L.length ≤ M)
    (h2 : n + L.length ≤ M) (h0 : Xsum (Vof (n := n) ψ) nb (chksD ψ.length L) = 0) : (evF S k pad i n Δ nb M (ψ, L)).toNat = nSat n ψ := by
  have h := (hEv Idx S ok hC k pad i n Δ nb M (ψ, L) hok hK hF ((hNP k (S.K i) n Δ nb M (ψ, L) hF).trans hfit.prof) hfit.net h1 h2).2 h0
  rw [h]
  have h3 := hProd (Fin n → Bool) (Fin ψ.length) (Vof (n := n) ψ) nb (chksD ψ.length L) h0
  have h4 : Fsum (Vof (n := n) (ψ, L).1) nb (chks (ψ, L)) = Fsum (Vof (n := n) ψ) nb (chksD ψ.length L) := rfl
  rw [h4, h3, Int.toNat_natCast, card_Vof]
end VariableBound.Count
