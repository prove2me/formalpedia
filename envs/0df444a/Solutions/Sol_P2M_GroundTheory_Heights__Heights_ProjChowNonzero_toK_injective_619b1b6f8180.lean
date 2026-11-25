-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_injective_619b1b6f8180
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:51.579784+00:00
-- url     : https://prove2.me/submissions/5a2a68c4-a3ba-4242-81a9-783b043b547f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero

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
open GroundTheory.Heights₂.Heights.ProjChowNonzero
namespace GroundTheory.Heights₂.Heights.ProjChowNonzero
theorem _root_.solution (e : ℕ) : Function.Injective (toK e) := by
  have h1 : Function.Injective (algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Loc e)) :=
    IsLocalization.injective (Loc e) (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))
  have h2 := IsFractionRing.injective (MvPolynomial (Fin (e + 1)) ℂ)
    (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
  exact (IsLocalization.lift_injective_iff _).mpr fun a b => h1.eq_iff.trans h2.eq_iff.symm
end GroundTheory.Heights₂.Heights.ProjChowNonzero
