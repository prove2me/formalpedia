-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.nonzeroLocus_secOfIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:18.145889+00:00
-- url     : https://prove2.me/submissions/abf02d8d-7469-4dfb-9de6-418955258a3e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_nonzeroLocus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_secOfIso_spec


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
theorem _root_.solution {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB)
    (hB : B.IsLB) : nonzeroLocus t ≤ nonzeroLocus (secOfIso (u := u) t hu hA hB) := by
  intro y hy
  obtain ⟨b, hb⟩ := (mem_nonzeroLocus t y).1 hy
  have hyb : y ∈ B.U b := Y.basicOpen_le _ hb
  obtain ⟨a, ha⟩ : ∃ a, y ∈ A.U a := by
    have : y ∈ (⨆ a, A.U a : Y.Opens) := by rw [hA.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  refine (mem_nonzeroLocus _ y).2 ⟨a, ?_⟩
  have e := secOfIso_spec (u := u) t hu hA hB a b
  have e2 := congrArg Y.basicOpen e
  rw [isoCand, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _), Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e2
  have hmem : y ∈ (A.U a ⊓ B.U b) ⊓ ((A.U a ⊓ B.U b) ⊓ Y.basicOpen (t.f b)) := ⟨⟨ha, hyb⟩, ⟨ha, hyb⟩, hb⟩
  rw [← e2] at hmem
  exact hmem.2
end ReciprocityTheory.ChartRestriction.G.DVR
