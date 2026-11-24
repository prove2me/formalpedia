-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_hermZpow_47ad9a4aea08
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:38.636025+00:00
-- url     : https://prove2.me/submissions/6471de81-0c95-4b5b-b4f9-ab9a557afd31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {A : HermLine ι} (hA : IsSmoothHerm A) (m : ℤ) :
    IsSmoothHerm (hermZpow A m) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have h : (hermZpow A (n : ℤ)).h = fun z => A.h z ^ n := funext fun z => zpow_natCast (A.h z) n
    unfold IsSmoothHerm
    rw [h]
    exact hA.pow n
  · have h : (hermZpow A (-(n : ℤ))).h = fun z => (A.h z ^ n)⁻¹ :=
      funext fun z => by rw [← zpow_natCast, ← zpow_neg]; rfl
    unfold IsSmoothHerm
    rw [h]
    exact (hA.pow n).inv fun z hz => (pow_pos (A.pos z hz) n).ne'
end GroundTheory.Heights₂.Heights.Inter
