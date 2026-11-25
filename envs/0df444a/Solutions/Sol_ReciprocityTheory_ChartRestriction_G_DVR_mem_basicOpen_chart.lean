-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.mem_basicOpen_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:07.40569+00:00
-- url     : https://prove2.me/submissions/92c5d2bb-25a1-41b5-90c5-e574e7a277f5

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
variable {Y : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {M : LB Y} (s : LB.Sec M) {y : Y} {d j : M.ι} (hd : y ∈ Y.basicOpen (s.f d))
    (hj : y ∈ M.U j) : y ∈ Y.basicOpen (s.f j) := by
  have hdU : y ∈ M.U d := Y.basicOpen_le _ hd
  have h1 : y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (inf_le_left : M.U d ⊓ M.U j ≤ M.U d)).op).hom (s.f d)) := by
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hdU, hj⟩, hd⟩
  rw [s.compat d j, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (M.g d j).isUnit,
    Scheme.basicOpen_res] at h1
  exact h1.2.2
end ReciprocityTheory.ChartRestriction.G.DVR
