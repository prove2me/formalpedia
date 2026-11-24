-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_torusChar_eq_8a9d063e55cf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:04.521414+00:00
-- url     : https://prove2.me/submissions/9604bd48-7ccb-4933-acf7-8cb09b1fce07

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaCubeParseval

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
open MeasureTheory Real ComplexConjugate
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaCubeParseval
namespace GroundTheory.Heights₂.Heights.KThetaCubeParseval
theorem _root_.solution {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = Complex.exp (((2 * π * ∑ i, (m i : ℝ) * u i : ℝ) : ℂ) * Complex.I) := by
  unfold torusChar
  congr 1
  push_cast
  ring
end GroundTheory.Heights₂.Heights.KThetaCubeParseval
