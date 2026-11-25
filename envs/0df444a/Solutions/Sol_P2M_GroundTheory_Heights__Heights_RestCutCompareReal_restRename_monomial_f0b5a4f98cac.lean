-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutCompareReal_restRename_monomial_f0b5a4f98cac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:33.384076+00:00
-- url     : https://prove2.me/submissions/f20dad67-4055-4452-a655-75655feca3b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCompareReal

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.RestCutCompareReal
namespace GroundTheory.Heights₂.Heights.RestCutCompareReal
theorem _root_.solution (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k)
    (α : Fin f × Fin N →₀ ℕ) (r : ℝ) :
    restRename f j k N e (monomial α r) = r • restTransport f j k N e (monomial α (1 : ℚ)) := by
  have h : (monomial α r : MvPolynomial (Fin f × Fin N) ℝ) =
      r • map (algebraMap ℚ ℝ) (monomial α (1 : ℚ)) := by
    rw [map_monomial, smul_monomial, map_one, smul_eq_mul, mul_one]
  rw [h, map_smul]
  rfl
end GroundTheory.Heights₂.Heights.RestCutCompareReal
