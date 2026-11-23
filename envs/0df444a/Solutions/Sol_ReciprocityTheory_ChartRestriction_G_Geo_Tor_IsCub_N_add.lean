-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub.N_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:38.620056+00:00
-- url     : https://prove2.me/submissions/3b582477-ec28-412f-a348-5b453065678b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat

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
theorem _root_.solution (k : ℕ) (a m x b : A) :
    cubN θ k a m (x * b) * θ a x b * θ m x b ^ k = θ (a * m ^ k) x b * cubN θ k a m x * cubN θ k a m b := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    have hc := h.compat (a * m ^ k) m x b
    unfold cubN at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, _root_.pow_succ,
      _root_.pow_succ, ← _root_.mul_assoc a]
    set Cxb := ∏ i ∈ Finset.range k, θ (a * m ^ i) m (x * b)
    set Cx := ∏ i ∈ Finset.range k, θ (a * m ^ i) m x
    set Cb := ∏ i ∈ Finset.range k, θ (a * m ^ i) m b
    calc Cxb * θ (a * m ^ k) m (x * b) * θ a x b * (θ m x b ^ k * θ m x b)
        = (Cxb * θ a x b * θ m x b ^ k) * (θ (a * m ^ k) m (x * b) * θ m x b) := by ac_rfl
      _ = (θ (a * m ^ k) x b * Cx * Cb) * (θ (a * m ^ k) m (x * b) * θ m x b) := by rw [ih]
      _ = Cx * Cb * (θ (a * m ^ k) m (x * b) * θ (a * m ^ k) x b * θ m x b) := by ac_rfl
      _ = Cx * Cb * (θ (a * m ^ k * m) x b * θ (a * m ^ k) m b * θ (a * m ^ k) m x) := by rw [← hc]
      _ = θ (a * m ^ k * m) x b * (Cx * θ (a * m ^ k) m x) * (Cb * θ (a * m ^ k) m b) := by ac_rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsCub
