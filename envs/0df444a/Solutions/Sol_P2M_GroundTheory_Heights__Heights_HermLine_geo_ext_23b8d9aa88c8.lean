-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermLine_geo_ext_23b8d9aa88c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:41.409428+00:00
-- url     : https://prove2.me/submissions/273d0304-d688-4d83-a31f-9453f48371d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.HermLine
namespace GroundTheory.Heights₂.Heights.HermLine
theorem _root_.solution {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
    {A B : Geo.HermLine κ} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  obtain ⟨a, h, _, _⟩ := A
  obtain ⟨b, h', _, _⟩ := B
  simp only at ha hh
  subst ha hh
  rfl
end GroundTheory.Heights₂.Heights.HermLine
