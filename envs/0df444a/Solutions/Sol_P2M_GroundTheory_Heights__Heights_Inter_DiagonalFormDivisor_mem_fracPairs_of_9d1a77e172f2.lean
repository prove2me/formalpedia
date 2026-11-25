-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_mem_fracPairs_of_9d1a77e172f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:44.318357+00:00
-- url     : https://prove2.me/submissions/ba2dfef3-c2b7-4616-b34a-345eeca6038a

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
theorem _root_.solution {c c' : (Σ k, ι k) → Φ} {γ : K → ℕ} {r q : MRing ι} {y y' : Φ} (hr : IsMultiHomog r γ)
    (hq : IsMultiHomog q γ) (h : aeval c q ≠ 0) (h' : aeval c' q ≠ 0) (e : aeval c r = aeval c q * y)
    (e' : aeval c' r = aeval c' q * y') : (y, y') ∈ fracPairs c c' :=
  ⟨γ, r, q, hr, hq, h, h', e, e'⟩
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
