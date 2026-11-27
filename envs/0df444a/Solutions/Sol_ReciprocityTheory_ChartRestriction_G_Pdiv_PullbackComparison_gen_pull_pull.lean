-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_pull_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:33:47.410029+00:00
-- url     : https://prove2.me/submissions/a8819a74-064c-43af-9446-c6d3f9af53fb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_exists_gen_transfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_base_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull_pull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
section Germs
end Germs
section Transfer
variable {X Y Z Y' : Scheme.{0}}
private theorem mem_pull_pull_lemma_2 (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y)
    (j : PUnit.{1} → PUnit.{1} → L.ι) (z : Z) :
    z ∈ ((L.pull a).pull b).U j ↔ a.base (b.base z) ∈ L.U (j PUnit.unit PUnit.unit) :=
  (mem_wchart_pu (L.pull a) b j z).trans (mem_wchart_pu L a (j PUnit.unit) (b.base z))
end Transfer
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {X Y Z Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
theorem _root_.solution (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (c : Y' ⟶ X) (d : Z ⟶ Y')
    (hbd : b ≫ a = d ≫ c) (h : ∃ t : LB.Gen ((L.pull a).pull b), t.IsGen) :
    ∃ t : LB.Gen ((L.pull c).pull d), t.IsGen := by
  have hmem : ∀ (j : PUnit.{1} → PUnit.{1} → L.ι) (z : Z),
      z ∈ ((L.pull c).pull d).U j → z ∈ ((L.pull a).pull b).U j := by
    intro j z hz
    rw [mem_pull_pull_lemma_2 L c d j z] at hz
    rw [mem_pull_pull_lemma_2 L a b j z]
    rw [base_eq hbd z]
    exact hz
  refine exists_gen_transfer (L := (L.pull a).pull b) (L' := (L.pull c).pull d) (fun j => j)
    (fun j z hz => hmem j z hz) ?_ h
  intro i j y hy
  have h1 : y ∈ (d ≫ c) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) :=
    ⟨(mem_pull_pull_lemma_2 L c d i y).1 hy.1, (mem_pull_pull_lemma_2 L c d j y).1 hy.2⟩
  have h2 : y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) := by
    rw [hbd]
    exact h1
  exact (germ_pull_pull L c d i j y hy h1).trans
    ((gU_pullU_congr hbd.symm _ _ y h1 h2).trans (germ_pull_pull L a b i j y _ h2).symm)
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
