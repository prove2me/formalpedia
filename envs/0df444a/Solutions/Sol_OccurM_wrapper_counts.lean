-- Prove2me | solution 1 for OccurM.wrapper_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:19:32.764476+00:00
-- url     : https://prove2.me/submissions/ff5f3616-7b48-481d-bc41-406ad1f71bdc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_OccurM_Wrapper
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_OccurM_bound_le_pow
import Theorems.Thm_OccurM_one_le_expClauses
import Theorems.Thm_OccurM_steps_le
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open OccurM
open Groundwork Turing MainTheoremForms ClausesOccur
open Sat3 (CNF)
namespace OccurM
theorem _root_.solution {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (code : ∀ (_ : ℕ) {V : ℕ}, CNF V → List Bool) {pre : List Bool → List Bool}
    (hpre : ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → ∃ ψ : CNF (numOcc φ), SatK.IsKCNF k ψ ∧ SatM.AllOccur ψ ∧ ψ.length = φ.length ∧
      SatK.numSat ψ = numSatOcc φ ∧ pre (code k φ) = SatM.enc k ψ)
    (hlen : ∀ (k V : ℕ) (φ : CNF V), 1 ≤ (code k φ).length)
    {M : TM2ComputableAux Bool Bool} {C : ℕ} (hM : SatM.CountsTM M (SatM.bound (SatM.rPow α) C))
    {N : TM2ComputableAux Bool Bool} {q : ℕ} (hW : Wrap.Wraps M pre id N q) :
    ∀ (k V : ℕ) (φ : CNF V), 1 ≤ k → SatK.IsKCNF k φ → 2 ≤ φ.length →
      Nonempty (TM2OutputsInTime N.tm ((code k φ).map N.inputAlphabet.invFun) (some ((SatK.binary (numOcc φ) (numSatOcc φ)).map N.outputAlphabet.invFun))
        (timeClauses α (stepsC q (2 * C + 1)) k φ.length + stepsC q (2 * C + 1) * (code k φ).length ^ stepsC q (2 * C + 1))) := by
  intro k V φ hk hφ hm
  obtain ⟨ψ, hψ, ho, e1, e2, e3⟩ := hpre k V φ hk hφ
  have hrun := hM k _ ψ hk (by omega) hψ ho
  rw [e1, e2, ← e3] at hrun
  obtain ⟨ev⟩ := hW (code k φ) _ _ hrun
  obtain ⟨E, hE1, hE2⟩ := bound_le_pow h0 h1 C hk hm
  refine ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩
  calc q * (SatM.bound (SatM.rPow α) C k φ.length + (code k φ).length + 1) ^ q ≤ q * ((code k φ).length + 2 ^ E + 1) ^ q :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ ≤ _ := steps_le q (2 * C + 1) hE2 (one_le_expClauses h0 h1 hk hm) (hlen k V φ)
end OccurM
