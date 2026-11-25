-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_lineVal_comb_27def6546364
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:33:46.89248+00:00
-- url     : https://prove2.me/submissions/fdc9a923-3d60-4a40-9e0a-77066c56449e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
set_option linter.unusedSectionVars false
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
theorem _root_.solution (e : Module.Basis (Fin 2) Ω E) (φ₀ φ₁ : E →ₗ[Ω] Ω) (c₀ c₁ : Ω) (b : Φ) :
    T.lineVal e (c₀ • φ₀ + c₁ • φ₁) b =
      algebraMap Ω Φ c₀ * T.lineVal e φ₀ b + algebraMap Ω Φ c₁ * T.lineVal e φ₁ b := by
  simp only [T.lineVal, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add, map_mul]
  ring
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
