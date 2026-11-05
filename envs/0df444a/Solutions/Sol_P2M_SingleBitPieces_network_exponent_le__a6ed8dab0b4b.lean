-- Prove2me | solution 1 for P2M_SingleBitPieces_network_exponent_le__a6ed8dab0b4b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:37:07.271476+00:00
-- url     : https://prove2.me/submissions/70276570-954a-4ad0-9451-5e8855f67eec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_Paper_SecProof_Proof
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Theorems.Thm_SingleBitPieces_network_exponent_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SingleBitPieces
open Groundwork Groundwork.Prog Finset Paper
namespace SingleBitPieces
theorem _root_.solution {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U ≤ 6 * m)
    (hP : g * P ≤ 6 * (m + g)) : δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K ≤ 3 / 4 * δ' * m + δ' * g := by
  have h := network_exponent_le hδ' h1 hK hU hP
  have hm : (0 : ℝ) ≤ δ' * m := by positivity
  have hg : (0 : ℝ) ≤ δ' * g := by positivity
  nlinarith
end SingleBitPieces
