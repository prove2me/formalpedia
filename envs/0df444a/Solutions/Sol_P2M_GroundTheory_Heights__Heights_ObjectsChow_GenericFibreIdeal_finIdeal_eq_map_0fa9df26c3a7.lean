-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_eq_map_0fa9df26c3a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:08.657567+00:00
-- url     : https://prove2.me/submissions/07f7c812-1b89-4cff-881f-7291d8aaa972

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
namespace GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
theorem _root_.solution (P : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = P.map (blkRingEquiv n).symm := by
  rw [Ideal.map_symm]
  exact Ideal.ext fun _ => Iff.rfl
end GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
