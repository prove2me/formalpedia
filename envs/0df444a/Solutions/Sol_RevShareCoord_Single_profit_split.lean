-- Prove2me | solution 1 for RevShareCoord.Single.profit_split
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:59:23.383272+00:00
-- url     : https://prove2.me/submissions/c0aa6926-6fcb-47f6-9cdb-2457694ee93b

import Mathlib
import Definitions.Def_RevShareCoord_Single_Model

open RevShareCoord.Single in
theorem solution (M : Model) (φ q : ℝ) :
    M.retailerProfit φ (φ * M.c) q = φ * M.Pi q ∧
      M.supplierProfit φ (φ * M.c) q = (1 - φ) * M.Pi q := by
  constructor <;>
  · simp only [Model.retailerProfit, Model.supplierProfit, Model.Pi]
    ring
