-- Prove2me | solution 1 for Occ.stSameAsFin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:06.002668+00:00
-- url     : https://prove2.me/submissions/e351fcc9-fcf1-4fdb-9a46-4a9e239061e5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Occ_Defs
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_CountKSat_InOut
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Int
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Definitions.Def_Occ_Main

set_option autoImplicit false
section
section
open Occ
open Groundwork Groundwork.Prog CountKSat
namespace Occ
theorem _root_.solution : StSameAsFin := fun N φ => by
  constructor
  · rw [numOcc, MainTheoremForms.numOcc, ← Nat.card_congr (occEquiv φ)]
    exact (Nat.subtype_card _ fun _ => Iff.rfl).symm
  · rw [Eight.numSat, MainTheoremForms.numSatOcc, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr ((Equiv.arrowCongr (occEquiv φ) (Equiv.refl Bool)).subtypeEquiv fun a => ?_)
    constructor
    · intro H C hC
      obtain ⟨l', hl', h, ha⟩ := H _ (List.mem_map_of_mem hC)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
      exact ⟨l, hl, (val_mem_occurring φ l.1).1 h, ha⟩
    · intro H C' hC'
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC'
      obtain ⟨l, hl, h, ha⟩ := H C hC
      exact ⟨_, List.mem_map_of_mem hl, (val_mem_occurring φ l.1).2 h, ha⟩
end Occ
