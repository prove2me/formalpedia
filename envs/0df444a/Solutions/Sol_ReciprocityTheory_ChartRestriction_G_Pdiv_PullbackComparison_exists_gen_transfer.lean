-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.exists_gen_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:01.556704+00:00
-- url     : https://prove2.me/submissions/0d4e75e2-3326-4c01-8794-61573f32a1ed

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res

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
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {X Y Z Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
theorem _root_.solution {L L' : LB X} (e : L'.ι → L.ι) (hU : ∀ j, L'.U j ≤ L.U (e j))
    (hg : ∀ i j (y : X) (hy : y ∈ L'.U i ⊓ L'.U j),
      gU y hy (L'.g i j) = gU y (⟨hU i hy.1, hU j hy.2⟩ : y ∈ L.U (e i) ⊓ L.U (e j)) (L.g (e i) (e j)))
    (h : ∃ t : LB.Gen L, t.IsGen) : ∃ t' : LB.Gen L', t'.IsGen := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun j => res (hU j) (t.s (e j))⟩, fun i j => ?_⟩
  apply unit_ext
  intro y hy
  have hm : y ∈ L.U (e i) ⊓ L.U (e j) := ⟨hU i hy.1, hU j hy.2⟩
  have key := congrArg (gU y hm) (ht (e i) (e j))
  simp only [map_mul, gU_res] at key ⊢
  rw [hg i j y hy]
  exact key
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
