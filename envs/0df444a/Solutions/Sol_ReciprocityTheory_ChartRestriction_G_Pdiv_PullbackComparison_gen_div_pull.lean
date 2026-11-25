-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_div_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:13.600195+00:00
-- url     : https://prove2.me/submissions/e026a979-1b77-4f56-b89c-91c355ad41c7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_exists_gen_transfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pull_g_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_base_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pull_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_germ_pullU_div
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
private theorem gU_pullU_comp_lemma (b : Z ⟶ Y) (a : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) (y : Z)
    (hy : y ∈ (b ≫ a) ⁻¹ᵁ U) :
    gU y hy (pullU (b ≫ a) U x) = gU y hy (pullU b (a ⁻¹ᵁ U) (pullU a U x)) := rfl
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
theorem _root_.solution (L : LB X) (sG : X ⟶ X) (φ₂ : Y ⟶ X) (sA : Y ⟶ Y) (h : sA ≫ φ₂ = φ₂ ≫ sG)
    (hw : ∃ t : LB.Gen ((LB.div (L.pull sG) L).pull φ₂), t.IsGen) :
    ∃ t : LB.Gen (LB.div ((L.pull φ₂).pull sA) (L.pull φ₂)), t.IsGen := by
  have hU : ∀ p : (LB.div ((L.pull φ₂).pull sA) (L.pull φ₂)).ι,
      (LB.div ((L.pull φ₂).pull sA) (L.pull φ₂)).U p ≤
        ((LB.div (L.pull sG) L).pull φ₂).U (fun _ => ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit)) := by
    intro p y hy
    have hy1 := (mem_pull_pull_lemma_2 L φ₂ sA p.1 y).1 hy.1
    have hy2 := (mem_wchart_pu L φ₂ p.2 y).1 hy.2
    refine (mem_wchart_pu (LB.div (L.pull sG) L) φ₂ (fun _ => ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit)) y).2 ⟨?_, hy2⟩
    refine (mem_wchart_pu L sG (fun _ => p.1 PUnit.unit PUnit.unit) (φ₂.base y)).2 ?_
    exact (congrArg (· ∈ L.U (p.1 PUnit.unit PUnit.unit)) (base_eq h y)).mp hy1
  refine exists_gen_transfer (L := (LB.div (L.pull sG) L).pull φ₂)
    (L' := LB.div ((L.pull φ₂).pull sA) (L.pull φ₂))
    (fun p _ => ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit)) hU ?_ hw
  intro p p' y hy
  have hA : y ∈ (sA ≫ φ₂) ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) :=
    ⟨(mem_pull_pull_lemma_2 L φ₂ sA p.1 y).1 hy.1.1, (mem_pull_pull_lemma_2 L φ₂ sA p'.1 y).1 hy.2.1⟩
  have hB : y ∈ φ₂ ⁻¹ᵁ (L.U (p.2 PUnit.unit) ⊓ L.U (p'.2 PUnit.unit)) :=
    ⟨(mem_wchart_pu L φ₂ p.2 y).1 hy.1.2, (mem_wchart_pu L φ₂ p'.2 y).1 hy.2.2⟩
  have hS : y ∈ (φ₂ ≫ sG) ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) := by
    exact (congrArg (fun φ => y ∈ φ ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit))) h).mp hA
  have hF : y ∈ φ₂ ⁻¹ᵁ (sG ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit))) := hS
  have hD : y ∈ φ₂ ⁻¹ᵁ ((L.pull sG).U (fun _ => p.1 PUnit.unit PUnit.unit) ⊓
      (L.pull sG).U (fun _ => p'.1 PUnit.unit PUnit.unit)) :=
    ⟨(mem_wchart_pu L sG (fun _ => p.1 PUnit.unit PUnit.unit) (φ₂.base y)).2 hF.1,
      (mem_wchart_pu L sG (fun _ => p'.1 PUnit.unit PUnit.unit) (φ₂.base y)).2 hF.2⟩
  have hC : y ∈ φ₂ ⁻¹ᵁ ((LB.div (L.pull sG) L).U ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit) ⊓
      (LB.div (L.pull sG) L).U ((fun _ => p'.1 PUnit.unit PUnit.unit), p'.2 PUnit.unit)) :=
    ⟨⟨hD.1, hB.1⟩, ⟨hD.2, hB.2⟩⟩
  have hL := (germ_div ((L.pull φ₂).pull sA) (L.pull φ₂) p p' y hy).trans
    (congrArg₂ (· * ·) ((germ_pull_pull L φ₂ sA p.1 p'.1 y ⟨hy.1.1, hy.2.1⟩ hA).trans
      (gU_pullU_congr h (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit)) y hA hS))
      (congrArg (·⁻¹) (germ_pull L φ₂ p.2 p'.2 y ⟨hy.1.2, hy.2.2⟩ hB)))
  have hc := ((congrArg (fun z => gU y hD (pullU φ₂ ((L.pull sG).U (fun _ => p.1 PUnit.unit PUnit.unit) ⊓ (L.pull sG).U (fun _ => p'.1 PUnit.unit PUnit.unit)) z))
      (pull_g_eq L sG (fun _ => p.1 PUnit.unit PUnit.unit) (fun _ => p'.1 PUnit.unit PUnit.unit))).trans
    (gU_pullU_res φ₂ (pull_inf_le L sG (fun _ => p.1 PUnit.unit PUnit.unit) (fun _ => p'.1 PUnit.unit PUnit.unit)) (pullU sG (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit))) y hD hF)).trans (gU_pullU_comp_lemma φ₂ sG (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit)) y hS).symm
  have hR := (germ_pull (LB.div (L.pull sG) L) φ₂ (fun _ => ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit)) (fun _ => ((fun _ => p'.1 PUnit.unit PUnit.unit), p'.2 PUnit.unit)) y ⟨hU p hy.1, hU p' hy.2⟩ hC).trans
    ((germ_pullU_div (L.pull sG) L φ₂ ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit) ((fun _ => p'.1 PUnit.unit PUnit.unit), p'.2 PUnit.unit) y hC hD hB).trans (congrArg₂ (· * ·) hc rfl))
  exact hL.trans hR.symm
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
