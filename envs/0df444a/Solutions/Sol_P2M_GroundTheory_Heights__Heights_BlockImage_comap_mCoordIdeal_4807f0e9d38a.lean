-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockImage_comap_mCoordIdeal_4807f0e9d38a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:26:23.739806+00:00
-- url     : https://prove2.me/submissions/16fbc5c5-9119-4876-8ae5-e15964f3c4ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_BirationalOfBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockImage_mConeMap_rename_12896742ddc3

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
theorem _root_.solution (y : Coord n → Ω) (k₀ : ι) :
    (Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀)) =
      Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) := by
  ext f
  simp only [Ideal.mem_comap, Geo.mCoordIdeal, RingHom.mem_ker]
  rw [mConeMap_rename]
  exact map_eq_zero_iff _ (rename_injective _ (const_injective k₀))
end GroundTheory.Heights₂.Heights.BlockImage
