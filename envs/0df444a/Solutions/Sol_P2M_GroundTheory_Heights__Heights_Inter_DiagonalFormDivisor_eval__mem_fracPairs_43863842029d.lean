-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_eval__mem_fracPairs_43863842029d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:41.553324+00:00
-- url     : https://prove2.me/submissions/dd075b94-553e-4eb9-9baa-4c5609519dec

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
theorem _root_.solution {R : Type} [CommRing R] (f : R →+* Φ) {c c' : (Σ k, ι k) → Φ}
    (hf : ∀ y, (f y, f y) ∈ fracPairs c c') {n : Type} (z z' : n → Φ) (hz : ∀ j, (z j, z' j) ∈ fracPairs c c')
    (G : MvPolynomial n R) : (eval₂ f z G, eval₂ f z' G) ∈ fracPairs c c' := by
  induction G using MvPolynomial.induction_on with
  | C y => simpa using hf y
  | add p q hp hq => simpa using add_mem hp hq
  | mul_X p j hp => simpa using mul_mem hp (hz j)
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
