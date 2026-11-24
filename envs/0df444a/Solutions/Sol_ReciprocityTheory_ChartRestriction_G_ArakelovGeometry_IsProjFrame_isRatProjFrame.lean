-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsProjFrame.isRatProjFrame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:01.565435+00:00
-- url     : https://prove2.me/submissions/0b2dee6f-3967-4630-b8f8-53a5f94e724e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
section Int
variable {ι : Type*}
end Int
section SlopeTestRemainingChoices
variable {ι : Type*}
end SlopeTestRemainingChoices
private theorem isIntegral_coneRing_rat_of_int {ι : Type*} (y : ι → Ω) {a : Polynomial Ω}
    (ha : IsIntegral (coneRing ℤ y) a) : IsIntegral (coneRing ℚ y) a := by
  obtain ⟨p, hpm, hp0⟩ := ha
  have hcomp : (algebraMap (coneRing ℚ y) (Polynomial Ω)).comp (coneRingIntToRat y) =
      algebraMap (coneRing ℤ y) (Polynomial Ω) := RingHom.ext fun _ => rfl
  refine ⟨p.map (coneRingIntToRat y), hpm.map _, ?_⟩
  rw [eval₂_map, hcomp]
  exact hp0
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
namespace IsProjFrame
theorem _root_.solution {x : κ → Ω} {e : Fin (D + 1) → κ} (h : IsProjFrame x e) :
    IsRatProjFrame x e := ⟨h.inj, h.free, fun i => isIntegral_coneRing_rat_of_int _ (h.integral i)⟩
end IsProjFrame
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
