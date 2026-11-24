-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_algebraMap_mvPolynomial_int_complex_a208a4dfdd5b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:27.0872+00:00
-- url     : https://prove2.me/submissions/a844d902-0986-4cd3-8afa-e596119923e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComplexMinimalPrimesContract
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComplexMinimalPrimesContract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (σ : Type) :
    algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) = MvPolynomial.map (Int.castRingHom ℂ) := by
  rw [MvPolynomial.algebraMap_def]
  congr 1
end GroundTheory.Heights₂.Heights.HilbertSamuel
