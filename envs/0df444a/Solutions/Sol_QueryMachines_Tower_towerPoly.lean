-- Prove2me | solution 1 for QueryMachines.Tower.towerPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:03:04.097367+00:00
-- url     : https://prove2.me/submissions/be57f2e9-09bc-4c88-9487-2e273d429e11

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Poly
import Definitions.Def_Tower_PolyTower

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork Groundwork.PolyT QueryMachines.QueryMachine
variable {Ctx Q G A : Type} [HasSize Ctx] [Enc Ctx] [Enc Q] [Enc G] [Enc A]
variable (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A) [IsPolyQ Sol] [IsPolyQ Inn]
variable [Carried Ctx]
namespace QueryMachines.Tower
theorem _root_.solution : TowerPoly := fun _ _ _ _ _ _ _ _ _ _ Sol Inn ⟨hS⟩ ⟨hI⟩ => ⟨@towerIsPoly _ _ _ _ _ _ _ _ _ Sol Inn hS hI _⟩
end QueryMachines.Tower
