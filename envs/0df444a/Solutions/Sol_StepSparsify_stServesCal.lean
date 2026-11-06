-- Prove2me | solution 1 for StepSparsify.stServesCal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:55:38.834789+00:00
-- url     : https://prove2.me/submissions/56080ec1-e5ef-4781-ba7a-e3498a30e9c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_CalNumbers
import Definitions.Def_StepSparsify_CalLeaves
import Definitions.Def_StepSparsify_CertThCal
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_UniformInK_Cert_Sparsify
import Definitions.Def_CountKSat_Poly
import Definitions.Def_StepSparsify_CalServes
import Theorems.Thm_StepSparsify_length_leaves_rootC
import Theorems.Thm_StepSparsify_polyT_stepCCal
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Cal_stThrCal
import Theorems.Thm_SparsificationLemma_stCountOfExactlyOne
import Theorems.Thm_SparsificationLemma_stExactlyOne
import Theorems.Thm_SparsificationLemma_stOutputsSame
import Theorems.Thm_SparsificationLemma_stTreeG
import Theorems.Thm_StepSparsify_stCalLeaves
import Theorems.Thm_StepSparsify_stCalNumbers


set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent UniformInK UniformInK.CertSparsify SparsificationLemma
namespace StepSparsify
theorem _root_.solution (hT : StCertThCal) : StServesCal where
  tree := by
    intro k n s hk hs ψ hψ _
    obtain ⟨n1, n2, n3, -⟩ := stCalNumbers k s hk hs
    have hD := Nat.mul_le_mul_right n n3
    obtain ⟨-, c2, c3, c4⟩ := stTreeG stExactlyOne stCountOfExactlyOne stOutputsSame k (alphaS k s) n (bsumU (tauOf s) k * n) (thCal k s)
      (Cal.betaC (alphaS k s)) hk n2 (Cal.stThrCal (alphaS k s) k n1) hD ψ hψ
    exact ⟨(length_leaves_rootC _ _ _ _ _).le.trans (stCalLeaves k n s _ ψ hk hD hψ), c2, c3, c4⟩
  par := fun k s hk hs => (stCalNumbers k s hk hs).2.2.2
  cert := fun _ _ _ _ _ hk h2 hs hx => polyT_stepCCal hT hk h2 hs hx
end StepSparsify
