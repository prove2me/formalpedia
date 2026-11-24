-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_finIdeal_eq_comap_eead2ee5270f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:46.027519+00:00
-- url     : https://prove2.me/submissions/e471f614-0dff-4719-8669-0c004be837e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreDim

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
open GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim
namespace GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim
theorem _root_.solution {n : ℕ} (P : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = P.comap (blkRingEquiv n) := by
  ext x
  rfl
end GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim
