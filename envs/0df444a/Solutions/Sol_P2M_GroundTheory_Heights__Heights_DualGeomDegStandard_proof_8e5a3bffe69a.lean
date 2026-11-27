-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualGeomDegStandard_proof_8e5a3bffe69a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:00:36.348287+00:00
-- url     : https://prove2.me/submissions/352e25be-efe5-4d5c-90ed-5c5740c5f100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ScaledExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegStandard

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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder
namespace GroundTheory.Heights₂.Heights
namespace DualGeomDegStandard
theorem _root_.solution (hD : DualGeomDegCharts.Statement)
    (hG : GrassGeomDegChart.Statement) (hM : ChartMassInvariant.Statement) :
    DualGeomDegStandard.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨A, hA, hE⟩ := hD K i F T b hb hi
  obtain ⟨B, hB, hG'⟩ := hG (i - 1)
  have e1 : 1 * 1 * (i - 1) = i - 1 := by simp
  have hterm : ∀ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ) =
      chartMass (1 : Matrix (Fin (i - 1 + 1)) (Fin (i - 1 + 1)) ℂ) := fun σ =>
    hM _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hA σ).1)
  rw [e1, hE, hG', hM _ _ (Matrix.PosDef.conjTranspose_mul_self B hB.1),
    Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, Finset.card_univ,
    Embeddings.card K ℂ, nsmul_eq_mul]
end DualGeomDegStandard
end GroundTheory.Heights₂.Heights
