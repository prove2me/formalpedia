-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PGaussFourierSelf_ofReal_gauss_3cb7d6e7b62c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:41.983696+00:00
-- url     : https://prove2.me/submissions/bd5f68db-5b0c-4d49-93d1-b4710fcaabf9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussFourierSelf

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
open Real MeasureTheory
open scoped FourierTransform
open GroundTheory.Heights₂.Heights.PGaussFourierSelf
namespace GroundTheory.Heights₂.Heights.PGaussFourierSelf
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] (x : V) :
    ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) = Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf
end GroundTheory.Heights₂.Heights.PGaussFourierSelf
