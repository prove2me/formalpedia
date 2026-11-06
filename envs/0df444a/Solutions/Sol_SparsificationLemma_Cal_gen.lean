-- Prove2me | solution 1 for SparsificationLemma.Cal.gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:32:31.889638+00:00
-- url     : https://prove2.me/submissions/4f27908b-6897-4734-b244-a1b24c0c4cb9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Facts
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_SparsificationLemma_Cal_stThrCal
import Theorems.Thm_SparsificationLemma_stGen
import Theorems.Thm_SparsificationLemma_stSide
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
namespace SparsificationLemma.Cal
theorem _root_.solution {α k n : ℕ} {ψ : PFml} (hα : 1 ≤ α) (hk : 1 ≤ k) (hψ : IsKCNF k n ψ) :
    (∀ x ∈ tree (thetaC α) k (depthC α k n) ψ, stepC (thetaC α) k x = none) ∧
    (outputs (thetaC α) k (depthC α k n) ψ).length ≤ ∑ j ∈ range ((k - 1) * n / α + 1), (depthC α k n).choose j ∧
    (∀ Φ ∈ outputs (thetaC α) k (depthC α k n) ψ, IsKCNF k n Φ ∧ ∀ v, occN Φ v ≤ 2 * (∑ j ∈ range k, thetaC α j) + 2) ∧
    ∀ x ∈ tree (thetaC α) k (depthC α k n) ψ, x.1.length ≤ ψ.length :=
  stGen stSide k α n (depthC α k n) (thetaC α) (betaC α) hk hα (stThrCal α k hα) (le_refl _) ψ hψ
end SparsificationLemma.Cal
