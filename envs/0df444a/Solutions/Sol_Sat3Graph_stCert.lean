-- Prove2me | solution 1 for Sat3Graph.stCert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:33:29.465295+00:00
-- url     : https://prove2.me/submissions/64bd84b7-fd0c-43b0-8e09-448a0354357d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_Sat3Graph_Sets
import Definitions.Def_Sat3Graph_Dominating
import Definitions.Def_Sat3Graph_Coloring
import Definitions.Def_Sat3Graph_Cert
import Definitions.Def_Sat3Graph_Host
import Definitions.Def_SizeCircuit_Circuit
import Definitions.Def_SizeCircuit_Cert
import Definitions.Def_Complement_Readers
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_GraphProblems_DomTree
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Main
import Theorems.Thm_Complement_stIndepAlone
import Theorems.Thm_Complement_stReadersCert
import Theorems.Thm_Sat3Graph_stCert_of


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement SplitSat
namespace Sat3Graph
theorem _root_.solution : StCert := stCert_of stReadersCert stIndepAlone
end Sat3Graph
