-- Prove2me | solution 1 for Sat3Graph.readC_polyT_alone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:23:39.93898+00:00
-- url     : https://prove2.me/submissions/e5850741-8f48-4a7f-86ce-b41cf8f1caf8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SizeCircuit_SizedCert
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Walk
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Cert
import Theorems.Thm_Sat3Graph_readC_behind_polyT
import Theorems.Thm_GraphProblems_stCertRead


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit Complement SplitSat
namespace Sat3Graph
theorem _root_.solution (k : ℕ) : PolyT (readC k) := readC_behind_polyT k stCertRead.1
end Sat3Graph
