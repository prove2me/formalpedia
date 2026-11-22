-- Prove2me | solution 1 for Paper.Hypergraph.trimDemand_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:43.25526+00:00
-- url     : https://prove2.me/submissions/b6df20bb-63bc-40fe-8d8c-934df74afa1d

import Definitions.Def_Paper_RoundingAveraging
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Paper_RoundingIndependence

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {x : ℕ → ℝ} (hx : H.UnitDemand x) (ε : ℝ) :
    H.UnitDemand (trimDemand x ε) := by
  intro v hv
  dsimp [trimDemand]
  split_ifs
  · exact ⟨le_min (by linarith [(hx v hv).1]) zero_le_one, min_le_right _ _⟩
  · norm_num
end Paper.Hypergraph
