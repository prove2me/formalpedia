-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.comm_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:26.398446+00:00
-- url     : https://prove2.me/submissions/68411718-99b8-4eec-8689-c22a4ee86329

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple

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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {M : Type*} [CommGroup M] (a b c : M) (n : ℤ) :
    (a * b⁻¹ * c) ^ (-n) = b ^ n * (a ^ n)⁻¹ * c ^ (-n) := by
  rw [mul_zpow, mul_zpow, zpow_neg a, inv_zpow', neg_neg, mul_comm ((a ^ n)⁻¹) (b ^ n)]
end ReciprocityTheory.ChartRestriction.G.DVR
