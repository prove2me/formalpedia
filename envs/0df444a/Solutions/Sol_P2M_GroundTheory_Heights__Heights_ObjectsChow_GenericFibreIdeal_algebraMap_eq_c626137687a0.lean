-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_algebraMap_eq_c626137687a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:03.368657+00:00
-- url     : https://prove2.me/submissions/2c82a759-6df1-41f0-b318-74ee631a30d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
open GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
variable {n : ℕ}
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
theorem _root_.solution :
    algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
  show MvPolynomial.map (algebraMap ℤ ℚ) = _
  rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]
end GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
