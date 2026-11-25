-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_ringKrullDim_quot_finIdeal_f12def14930b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:59.372058+00:00
-- url     : https://prove2.me/submissions/ce92c737-743c-4aa0-8fdc-d8397043389e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreDim_finIdeal_eq_comap_eead2ee5270f

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
    ringKrullDim (MvPolynomial (Fin n) ℤ ⧸ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) =
      ringKrullDim (MRing (PBlk n) ⧸ P) := by
  rw [finIdeal_eq_comap]
  refine ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquiv (P.comap (blkRingEquiv n)) P (blkRingEquiv n) ?_)
  exact (Ideal.map_comap_of_surjective _ (blkRingEquiv n).surjective P).symm
end GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim
