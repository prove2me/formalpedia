-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub.N_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:30.026953+00:00
-- url     : https://prove2.me/submissions/dc47e961-f1fe-4cd2-a586-2bd51e2c4bd3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
variable {A U : Type} [CommGroup A] [CommGroup U]
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
variable {θ : A → A → A → U} (h : IsCub θ)
include h
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
theorem _root_.solution (k : ℕ) (a m x : A) : cubN θ k a m x = θ a (m ^ k) x * cubN θ k 1 m x := by
  induction k with
  | zero => simp [cubN, h.face₂]
  | succ k ih =>
    have hc := h.coc a (m ^ k) m x
    unfold cubN at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih, _root_.one_mul, _root_.pow_succ]
    set P := ∏ i ∈ Finset.range k, θ (1 * m ^ i) m x
    calc θ a (m ^ k) x * P * θ (a * m ^ k) m x = P * (θ (a * m ^ k) m x * θ a (m ^ k) x) := by ac_rfl
      _ = P * (θ a (m ^ k * m) x * θ (m ^ k) m x) := by rw [hc]
      _ = θ a (m ^ k * m) x * (P * θ (m ^ k) m x) := by ac_rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
