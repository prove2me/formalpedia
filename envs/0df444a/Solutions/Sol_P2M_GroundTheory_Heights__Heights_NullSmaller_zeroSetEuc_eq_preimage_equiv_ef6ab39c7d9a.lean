-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NullSmaller_zeroSetEuc_eq_preimage_equiv_ef6ab39c7d9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:58.381088+00:00
-- url     : https://prove2.me/submissions/49aa351b-ea3f-4541-a9a6-3b9a943802d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller

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
open MvPolynomial MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace NullSmaller
theorem _root_.solution {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSetEuc J =
      (EuclideanSpace.equiv (Fin n) ℂ) ⁻¹' {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} := by
  ext z
  rfl
end NullSmaller
end GroundTheory.Heights₂.Heights
