-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sphereMean_fubini
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:47:07.923734+00:00
-- url     : https://prove2.me/submissions/97ea42ef-c99d-42fb-886d-d5b53107205a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightProdPowMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SphereMeanSubstitutedEqIntegral
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_blockPoint_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_mpSplit
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sphereLogIntegrable
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSphereMeasure_isProbability
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphereMeasure_isProbability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution {F : MvPolynomial (Fin (d.D + 1) × Fin (d.N + 1)) ℂ} {a : Fin (d.D + 1) → ℕ}
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    blockSphereMean (d.D + 1) (d.N + 1) F =
      ∫ z, (∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) F‖ ∂(sphereProb (d.N + 1)))
        ∂(blockSphereProb d.D (d.N + 1)) := by
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  set G : UnitSphereC (d.N + 1) × BlockSphere d.D (d.N + 1) → ℝ :=
    fun p => Real.log ‖MvPolynomial.eval (hintPt (spherePoint p.1) p.2) F‖ with hG
  have hmp := hint_mpSplit d.D (d.N + 1) hn
  have hint : Integrable G ((sphereProb (d.N + 1)).prod (blockSphereProb d.D (d.N + 1))) := by
    rw [← hmp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d.D + 1) => UnitSphereC (d.N + 1)) 0).measurableEmbedding]
    refine (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable (d.D + 1) (d.N + 1) a F hF0 hF).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp_apply, hG]
    rw [hint_blockPoint_eq]
    rfl
  rw [← integral_prod_symm G hint]
  unfold blockSphereMean
  rw [← hmp.integral_comp
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d.D + 1) => UnitSphereC (d.N + 1)) 0).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hG]
  rw [hint_blockPoint_eq]
  rfl
end ReciprocityTheory.ChartRestriction.G.T0.Data
