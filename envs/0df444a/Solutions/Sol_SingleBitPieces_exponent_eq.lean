-- Prove2me | solution 1 for SingleBitPieces.exponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:58:30.324108+00:00
-- url     : https://prove2.me/submissions/345c31aa-4b96-477b-a28a-7b5179ba2f3d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Networks
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping

set_option autoImplicit false
section
section
open SingleBitPieces
open Groundwork Groundwork.Prog Finset Paper NetE Stepped
namespace SingleBitPieces
theorem _root_.solution (e U g P K : ℝ) : e * U + (e + 2) * (g * P) / K = e * (U + g * P / K) + 2 * g * P / K := by ring
end SingleBitPieces
