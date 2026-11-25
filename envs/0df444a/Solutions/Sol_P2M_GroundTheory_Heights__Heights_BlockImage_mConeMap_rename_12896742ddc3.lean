-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockImage_mConeMap_rename_12896742ddc3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:11:57.978803+00:00
-- url     : https://prove2.me/submissions/1728edfe-1a8f-45e4-be91-0bd1a799b344

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_BirationalOfBlock

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
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.BlockImage
theorem _root_.solution (y : Coord n → Ω) (k₀ : ι)
    (f : MvPolynomial (Coord fun _ : Unit ↦ n k₀) ℤ) :
    Geo.mConeMap (ι := blockIdx n) y (rename (blockIncl k₀) f) =
      rename (fun _ : Unit ↦ k₀)
        (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) f) := by
  have h : ((Geo.mConeMap (ι := blockIdx n) y).comp (rename (blockIncl k₀))) =
      ((rename (R := Ω) (fun _ : Unit ↦ k₀)).restrictScalars ℤ).comp
        (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) := by
    refine MvPolynomial.algHom_ext fun v ↦ ?_
    simp [Geo.mConeMap, blockIncl]
  exact congrArg (fun φ : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι Ω ↦ φ f) h
end GroundTheory.Heights₂.Heights.BlockImage
