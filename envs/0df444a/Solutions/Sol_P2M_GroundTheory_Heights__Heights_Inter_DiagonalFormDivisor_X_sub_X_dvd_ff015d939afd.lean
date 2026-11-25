-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_X_sub_X_dvd_ff015d939afd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:34.507793+00:00
-- url     : https://prove2.me/submissions/771ba8a8-3ccb-423f-a61b-ec0ac7c1233f

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
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
theorem _root_.solution {R : Type} [CommRing R] (P : MvPolynomial (Fin 2) R) :
    (X 1 - X 0 : MvPolynomial (Fin 2) R) ∣ P - aeval (fun _ => (X 0 : MvPolynomial (Fin 2) R)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p n hp =>
    rw [map_mul, aeval_X]
    have e : p * X n - aeval (fun _ => (X 0 : MvPolynomial (Fin 2) R)) p * X 0 =
        (p - aeval (fun _ => (X 0 : MvPolynomial (Fin 2) R)) p) * X n +
          aeval (fun _ => (X 0 : MvPolynomial (Fin 2) R)) p * (X n - X 0) := by ring
    rw [e]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    fin_cases n
    · simp
    · exact dvd_rfl
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
