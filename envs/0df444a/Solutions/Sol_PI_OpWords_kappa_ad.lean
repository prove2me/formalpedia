-- Prove2me | solution 1 for PI.OpWords.kappa_ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:39.047331+00:00
-- url     : https://prove2.me/submissions/213ecdd9-9118-4181-ab17-3728537c5a2c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_DivideAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution (hL : KappaLeft) (hR : KappaRight) (K : Type) [Field K] [CharZero K] (k d : ℕ)
    (a b : Fin k) (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d (Formalism.MainNotions.TestSideCounting.Ed K k d a b * A - A * Formalism.MainNotions.TestSideCounting.Ed K k d a b) =
      Rop K k a b (kappa K k d A) := by
  rw [map_sub, hL K k d a b A, hR K k d a b A]
  rfl
end PI.OpWords
