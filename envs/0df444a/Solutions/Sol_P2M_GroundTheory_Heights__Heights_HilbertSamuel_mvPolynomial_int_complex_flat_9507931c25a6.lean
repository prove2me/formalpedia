-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_mvPolynomial_int_complex_flat_9507931c25a6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:44.212575+00:00
-- url     : https://prove2.me/submissions/cf4d7782-70fa-4677-8469-15b81f33f050

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
    Module.Flat (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) :=
  Module.Flat.isBaseChange ℤ (MvPolynomial σ ℤ) ℂ (MvPolynomial σ ℂ)
    (Algebra.IsPushout.out (R := ℤ) (S := MvPolynomial σ ℤ) (R' := ℂ) (S' := MvPolynomial σ ℂ))
end GroundTheory.Heights₂.Heights.HilbertSamuel
