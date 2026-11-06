-- Prove2me | solution 1 for SplitSat.stReduceCert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:39:32.53678+00:00
-- url     : https://prove2.me/submissions/f75e7c5d-b400-4a06-9ad9-a2c2532c942b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_CountKSat_InOut
import Definitions.Def_SplitSat_Cert
import Theorems.Thm_SplitSat_reduceCore_polyTimeSteps
import Theorems.Thm_CountKSat_stCertDecU
import Theorems.Thm_WidthK_Prog_certStep


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight.Width
namespace SplitSat
theorem _root_.solution : StReduceCert := fun k τ D hD => by
  obtain ⟨h⟩ := reduceCore_polyTimeSteps (certStep (thetaU τ) k) hD
  exact ⟨IsPolyT.mapIn (stCertDecU k)⟩
end SplitSat
