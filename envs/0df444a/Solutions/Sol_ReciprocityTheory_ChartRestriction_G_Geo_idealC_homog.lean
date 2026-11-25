-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.idealC_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:06:00.942171+00:00
-- url     : https://prove2.me/submissions/7d1adb28-4f2c-4a86-b4a7-f2b493108fca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isWeightedHomogeneous_map_of_isMultiHomog


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)]
variable {e : ℕ}
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    (idealC ι P).IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hP
  rw [idealC, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨a, ha⟩ := hS g hg
  exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_map_of_isMultiHomog ha)⟩
end ReciprocityTheory.ChartRestriction.G.Geo
