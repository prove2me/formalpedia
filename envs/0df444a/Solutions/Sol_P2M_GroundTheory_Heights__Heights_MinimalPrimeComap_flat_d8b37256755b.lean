-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MinimalPrimeComap_flat_d8b37256755b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:45.935348+00:00
-- url     : https://prove2.me/submissions/53a817ed-a0d2-44cb-9645-e526eebe0df0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMinimalPrimeComap

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
namespace GroundTheory.Heights₂.Heights
namespace MinimalPrimeComap
theorem _root_.solution (K L : Type) [Field K] [Field L] (σ : K →+* L) (ι : Type) :
    let := σ.toAlgebra
    let := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
    Module.Flat (MvPolynomial ι K) (MvPolynomial ι L) := by
  let := σ.toAlgebra
  let := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have h : Algebra.IsPushout K (MvPolynomial ι K) L (MvPolynomial ι L) := inferInstance
  exact Module.Flat.isBaseChange K (MvPolynomial ι K) L (MvPolynomial ι L) h.out
end MinimalPrimeComap
end GroundTheory.Heights₂.Heights
