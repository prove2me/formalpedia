-- Prove2me | solution 1 for SplitSat.stSATsplit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:51:22.078748+00:00
-- url     : https://prove2.me/submissions/16001b50-8f5d-4793-beed-702d26e7c332

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Reader
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_SplitSat_Main
import Theorems.Thm_SplitSat_exists_parameters
import Theorems.Thm_SplitSat_stCore3


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping
open scoped NNReal ENNReal
namespace SplitSat
theorem _root_.solution : StSATsplit := fun k hk δ hδ => by
  obtain ⟨τ, δ₃, h0, h⟩ := exists_parameters k hk δ hδ
  obtain ⟨ℓ₃, τ₃, hp, c, hD⟩ := stCore3 δ₃ h0
  exact ⟨τ, ℓ₃, τ₃, h (core3 ℓ₃ τ₃) c hp hD⟩
end SplitSat
