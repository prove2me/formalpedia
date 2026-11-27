-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.gen_div_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:38:54.58589+00:00
-- url     : https://prove2.me/submissions/ec3941bf-d451-44a9-9ae2-65c322f36a03

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PullbackSquarePartialSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_exists_gen_transfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_genPull


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU exists_gen_transfer germ_pull germ_div)
variable {X Y : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution (M N : LB X) (a : Y ⟶ X) (h : ∃ t : LB.Gen (LB.div M N), t.IsGen) :
    ∃ t : LB.Gen (LB.div (M.pull a) (N.pull a)), t.IsGen := by
  obtain ⟨t, ht⟩ := h
  have hU : ∀ p : (LB.div (M.pull a) (N.pull a)).ι,
      (LB.div (M.pull a) (N.pull a)).U p ≤
        ((LB.div M N).pull a).U (fun u => (p.1 u, p.2 u)) := by
    intro p y hy
    obtain ⟨h1, h2⟩ := hy
    exact mem_pull_of_lemma_2 (LB.div M N) a (fun u => (p.1 u, p.2 u)) y
      (And.intro (mem_pull_lemma M a p.1 y h1) (mem_pull_lemma N a p.2 y h2))
  refine exists_gen_transfer (L := (LB.div M N).pull a) (L' := LB.div (M.pull a) (N.pull a))
    (fun p u => (p.1 u, p.2 u)) hU ?_ ⟨LB.genPull _ t a, LB.isGen_genPull _ t ht a⟩
  intro i j y hy
  obtain ⟨⟨hMi, hNi⟩, ⟨hMj, hNj⟩⟩ := id hy
  have hMi' := mem_pull_lemma M a i.1 y hMi
  have hNi' := mem_pull_lemma N a i.2 y hNi
  have hMj' := mem_pull_lemma M a j.1 y hMj
  have hNj' := mem_pull_lemma N a j.2 y hNj
  have hM : y ∈ a ⁻¹ᵁ (M.U (i.1 PUnit.unit) ⊓ M.U (j.1 PUnit.unit)) := And.intro hMi' hMj'
  have hN : y ∈ a ⁻¹ᵁ (N.U (i.2 PUnit.unit) ⊓ N.U (j.2 PUnit.unit)) := And.intro hNi' hNj'
  have hD : y ∈ a ⁻¹ᵁ ((LB.div M N).U (i.1 PUnit.unit, i.2 PUnit.unit) ⊓
      (LB.div M N).U (j.1 PUnit.unit, j.2 PUnit.unit)) :=
    And.intro (And.intro hMi' hNi') (And.intro hMj' hNj')
  refine (germ_div _ _ i j y hy).trans ?_
  refine Eq.trans (congrArg₂ (fun u v => u * v⁻¹)
    ((germ_pull M a i.1 j.1 y (And.intro hMi hMj) hM).trans (gU_pullU a _ y hM _))
    ((germ_pull N a i.2 j.2 y (And.intro hNi hNj) hN).trans (gU_pullU a _ y hN _))) ?_
  refine Eq.trans ?_ ((germ_pull (LB.div M N) a (fun u => (i.1 u, i.2 u))
    (fun u => (j.1 u, j.2 u)) y _ hD).trans (gU_pullU a _ y hD _)).symm
  refine Eq.trans ?_ (congrArg (Units.map _) (germ_div M N _ _ _ hD)).symm
  simp only [map_mul, map_inv]
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
