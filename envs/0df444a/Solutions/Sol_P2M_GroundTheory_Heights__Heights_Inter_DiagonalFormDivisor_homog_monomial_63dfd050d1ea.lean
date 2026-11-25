-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_homog_monomial_63dfd050d1ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:45.298737+00:00
-- url     : https://prove2.me/submissions/b7720f1d-a69d-465f-9fba-3579d1911a77

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
theorem _root_.solution (i : ι) (l : ν) (k : κ) (n₁ n₂ n₃ n₄ : ℕ) :
    IsMultiHomog (X ⟨.base, i⟩ ^ n₁ * X ⟨.det, l⟩ ^ n₂ * X ⟨.line0, k⟩ ^ n₃ * X ⟨.line1, k⟩ ^ n₄ :
      MRing (T.wwIdx ι ν κ)) (blockScale n₁ n₂ n₃ n₄) := by
  have h := exHomog_mul (exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base i) n₁)
    (exHomog_pow (exHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.det l) n₂))
    (exHomog_pow (exHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k) n₃))
    (exHomog_pow (exHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line1 k) n₄)
  convert h using 1
  funext b
  cases b <;> simp [blockScale]
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
