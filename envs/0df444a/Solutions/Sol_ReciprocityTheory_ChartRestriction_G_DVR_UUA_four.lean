-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.UUA.four
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:28.664799+00:00
-- url     : https://prove2.me/submissions/d3af8f2e-6996-4359-95d7-3a89e0b2c961

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPowAlg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CubicNormMulIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA
theorem _root_.solution (h : IsCub θ) (P q B b x : A) :
    θ (P * B) (q * b) x * θ P B x * θ q b x = θ (P * q) (B * b) x * θ P q x * θ B b x := by
  have c1 := h.coc P B (q * b) x
  have c2 := h.coc B q b x
  have c3 := h.coc P q (B * b) x
  have c4 := h.coc q B b x
  rw [mul_left_comm B q b] at c1
  rw [mul_comm q B, h.s01 q B x] at c4
  calc θ (P * B) (q * b) x * θ P B x * θ q b x
      = θ P (q * (B * b)) x * (θ B (q * b) x * θ q b x) := by rw [c1, mul_assoc]
    _ = θ P (q * (B * b)) x * (θ q (B * b) x * θ B b x) := by rw [← c2, c4]
    _ = θ (P * q) (B * b) x * θ P q x * θ B b x := by rw [c3, mul_assoc]
end ReciprocityTheory.ChartRestriction.G.DVR.UUA
