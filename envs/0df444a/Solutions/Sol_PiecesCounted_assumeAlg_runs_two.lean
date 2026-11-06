-- Prove2me | solution 1 for PiecesCounted.assumeAlg_runs_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:11.553423+00:00
-- url     : https://prove2.me/submissions/b30f1dc3-62e3-4b5e-8960-c51b889e60fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed
import Theorems.Thm_Groundwork_Stepped_bind_runs
import Theorems.Thm_Groundwork_Stepped_branch_runs_inr
import Theorems.Thm_Groundwork_Stepped_mapIn_runs


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
theorem _root_.solution {Alg : Stepped (List Unit × Question) Answer} {g g' : List Unit × Question} {a₀ a : Answer} {t t' S S' : ℕ} (h1 : Alg.Runs (firstQ g) t S a₀)
    (h2 : afterFirst (g, a₀) = .inr g') (h3 : Alg.Runs g' t' S' a) : (assumeAlg Alg).Runs g (t + 1 + t') (max (size g + S) (S' + 1) + 1) a :=
  Stepped.bind_runs (Stepped.mapIn_runs h1) (Stepped.branch_runs_inr h2 h3)
end PiecesCounted
