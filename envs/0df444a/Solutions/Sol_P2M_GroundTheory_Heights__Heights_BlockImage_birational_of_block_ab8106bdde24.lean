-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockImage_birational_of_block_ab8106bdde24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:11:52.801466+00:00
-- url     : https://prove2.me/submissions/6aeea601-4e36-4b10-806c-062465164039

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_BirationalOfBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.BlockImage
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {Ω : Type} [Field Ω]
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.BlockImage
theorem _root_.solution (y : Coord n → Ω) (k₀ : ι)
    (hB : Geo.Birational (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) :
    Geo.Birational (ι := blockIdx n) y := by
  intro s
  obtain ⟨d, g, h, hg, hh, hne, heq⟩ := hB s
  have hom : ∀ f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ,
      Geo.IsMultiHomog (ι := blockIdx fun _ : Unit ↦ n k₀) f d →
      Geo.IsMultiHomog (ι := blockIdx n) (rename (blockIncl k₀) f)
        (Function.extend (fun _ : Unit ↦ k₀) d 0) := by
    intro f hf
    rw [← Bridge.isMultiHomog_iff] at hf ⊢
    have hf' : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ n k₀) f d := hf
    rw [← hf'.weightedHomogeneousComponent_same, rename_component]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  refine ⟨Function.extend (fun _ : Unit ↦ k₀) d 0, rename (blockIncl k₀) g, rename (blockIncl k₀) h,
    hom g hg, hom h hh, ?_, ?_⟩
  · rw [aeval_rename]
    exact hne
  · rw [aeval_rename, aeval_rename]
    exact heq
end GroundTheory.Heights₂.Heights.BlockImage
