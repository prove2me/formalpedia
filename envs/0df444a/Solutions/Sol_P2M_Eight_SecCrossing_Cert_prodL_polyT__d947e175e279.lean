-- Prove2me | solution 1 for P2M_Eight_SecCrossing_Cert_prodL_polyT__d947e175e279
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:18:33.745192+00:00
-- url     : https://prove2.me/submissions/a9e98f27-5a8c-4bfc-9a39-cd5768c65fdb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_MulOut
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_Eight_SecCrossing_Cert
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_PaddedDescent_F_prodL_eq


set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F ClauseBound.Alg SingleBitPieces.SecCrossing_PolyA
open Eight.SecCrossing_Cert
variable {α : Type} [Enc α]
namespace Eight.SecCrossing_Cert
theorem _root_.solution {n : α → ℕ} {f : α → ℕ → ℤ} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => prodL (n x) (f x) :=
  (prodL_polyT (f := fun x s => f x (min s (n x))) hn hf).congr fun x => by
    rw [prodL_eq, prodL_eq]
    exact Finset.prod_congr rfl fun s hs => by rw [min_eq_left (Finset.mem_range.1 hs).le]
end Eight.SecCrossing_Cert
