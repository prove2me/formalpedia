-- Prove2me | solution 1 for P2M_GeneralPieces_Series_kappa__sum_5bc6c6120ed7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:42:32.553945+00:00
-- url     : https://prove2.me/submissions/f5ad15da-17c1-4525-aeb2-15f9f8fb60ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
import Theorems.Thm_GeneralPieces_Series_displayGamma_M
import Theorems.Thm_GeneralPieces_Series_leftGamma_M

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial
namespace GeneralPieces.Series
theorem _root_.solution {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (sumM j n fun k => (k : ℚ) * (Ring.choose (k - 1) (j - 1) : ℤ) * (Ring.choose (-k - 1) (n - 1) : ℤ)) = (ClauseBound.Boson.Gam j n : ℚ) • epsM ^ (j + n) := by
  rw [← leftGamma_M hj hn, displayGamma_M hj hn]
end GeneralPieces.Series
