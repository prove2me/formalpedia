-- Prove2me | solution 1 for P2M_GeneralPieces_Ring_sum_tup_succ__ab6e7a7dfbc1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:18:16.896394+00:00
-- url     : https://prove2.me/submissions/e9a616bc-6159-4c3d-9761-3191d1182edc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset
namespace GeneralPieces.Ring
theorem _root_.solution {A : Type} [AddCommMonoid A] (M q : ℕ) (G : List ℤ → A) :
    ∑ ks ∈ ClauseBound.Boson.tup M (q + 1), G ks = ∑ k ∈ ClauseBound.Boson.win M, ∑ ks ∈ ClauseBound.Boson.tup M q, G (k :: ks) := by
  rw [ClauseBound.Boson.tup, sum_image, sum_product]
  rintro ⟨k, ks⟩ _ ⟨k', ks'⟩ _ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.1 h.2
end GeneralPieces.Ring
