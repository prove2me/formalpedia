-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_subalgebra_isAlgebraic_int_021dcf6f6296
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:24.073118+00:00
-- url     : https://prove2.me/submissions/15715e11-ec29-4a60-b039-4a981fce82c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal

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
open NumberField Polynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {K : Type} [Field K] [NumberField K] (O : Subalgebra ℤ K)
    (y : O) : IsAlgebraic ℤ y := by
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hK : IsAlgebraic ℤ (y : K) :=
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (y : K))).restrictScalars (R := ℤ)
  exact (isAlgebraic_algHom_iff O.val Subtype.val_injective).mp hK
end GroundTheory.Heights₂.Heights
