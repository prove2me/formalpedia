-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.smallness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:47:46.607936+00:00
-- url     : https://prove2.me/submissions/f2d318d9-1219-448d-8fe7-1a11e1be5774

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_alpha_one_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (Delta : ℕ) (b : ℝ) (hb : 0≤b) (hq : alpha Delta*b<1) :
    0≤b ∧ b≤alpha Delta*b ∧ b<1 := by
  have he : b≤alpha Delta*b := by
    calc
      b = 1*b := by ring
      _ ≤ alpha Delta*b := mul_le_mul_of_nonneg_right (alpha_one_le Delta) hb
  exact ⟨hb,he,lt_of_le_of_lt he hq⟩
end QEC.Locality.WeightedConnectedSetMass
