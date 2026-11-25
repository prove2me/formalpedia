-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isHomogeneous_of_mem_minimalPrimes_21910d679847
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:42.925388+00:00
-- url     : https://prove2.me/submissions/39d5552d-22d0-4048-9741-f78137c35987

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivCyclePrime

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
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {I P : Ideal (MvPolynomial (Fin n) ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ)) (hP : P ∈ I.minimalPrimes) :
    P.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  have hcore : (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal.IsPrime :=
    hP.1.1.homogeneousCore
  have hle : I ≤ (P.homogeneousCore (homogeneousSubmodule (Fin n) ℂ)).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hP.1.2)
  have hcoreP := Ideal.toIdeal_homogeneousCore_le (homogeneousSubmodule (Fin n) ℂ) P
  rw [Ideal.IsHomogeneous.iff_eq]
  exact le_antisymm hcoreP (hP.2 ⟨hcore, hle⟩ hcoreP)
end GroundTheory.Heights₂.Heights
