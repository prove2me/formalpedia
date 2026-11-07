-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.geometric_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:53:02.736126+00:00
-- url     : https://prove2.me/submissions/eac967bf-fd0e-43be-8b76-4afca057f050

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_geometric_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (q : ℝ) (l n : ℕ) (h0 : 0≤q) (hq : q≤1/2) :
    geometric q l n ≤ 2*q^l := by
  have ht := geometric_le q l n h0 (by linarith)
  have hden : 0<1-q := by linarith
  have he : q^l/(1-q) ≤ 2*q^l := (div_le_iff₀ hden).mpr (by
    nlinarith [mul_nonneg (pow_nonneg h0 l) (show 0≤1-2*q by linarith)])
  exact ht.trans he
end QEC.Locality.WeightedConnectedSetMass
