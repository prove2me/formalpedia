-- Prove2me | solution 1 for UniformInK.End.boundNK_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:32.7314+00:00
-- url     : https://prove2.me/submissions/329f8c50-68c4-4a8c-bc99-cf233035179f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_UniformInK_Top_End

set_option autoImplicit false
section
section
open UniformInK UniformInK.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End
namespace UniformInK.End
theorem _root_.solution {r : ℕ → ℝ} {D D' : ℕ} (h : D ≤ D') (k n : ℕ) (hr : 0 ≤ r n) : SatM.boundNK r D k n ≤ SatM.boundNK r D' k n := by
  unfold SatM.boundNK
  have hD : (D : ℝ) ≤ D' := by exact_mod_cast h
  refine Nat.floor_le_floor (mul_le_mul hD (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (by positivity) (by positivity))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (by positivity)) (by positivity)) hr
end UniformInK.End
