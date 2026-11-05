-- Prove2me | solution 1 for VariableBound.Fld.isFamily_comap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:21:55.856766+00:00
-- url     : https://prove2.me/submissions/f8675975-b8a6-45bc-a8ed-761c086f8538

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Definitions.Def_VariableBound_Field_Transfer

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset
namespace VariableBound.Fld
theorem _root_.solution {E ι ι' : Type} [Fintype E] [DecidableEq E] {v : ℕ} {Ω : Finset ι} {Γ : ι → Finset E} (h : AppVariables.IsFamily v Ω Γ)
    (φ : ι' ↪ ι) (Ω' : Finset ι') (hΩ : Ω = Ω'.map φ) : AppVariables.IsFamily v Ω' fun i => Γ (φ i) := by
  subst hΩ
  refine ⟨fun u hu => h.a _ (Finset.mem_map_of_mem φ hu), fun e => ?_, fun V hV => ?_⟩
  · have := h.b e
    rwa [Finset.filter_map, Finset.card_map, Finset.card_map] at this
  · have := h.c V hV
    rwa [Finset.filter_map, Finset.card_map, Finset.card_map] at this
end VariableBound.Fld
