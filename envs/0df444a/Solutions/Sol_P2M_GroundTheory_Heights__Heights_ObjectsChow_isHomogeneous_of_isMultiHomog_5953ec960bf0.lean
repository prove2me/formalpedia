-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_isHomogeneous_of_isMultiHomog_5953ec960bf0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:21.481221+00:00
-- url     : https://prove2.me/submissions/b5e07fca-fb07-45e4-8a17-689bee8da928

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsHomogeneousOfIsMultiHomog

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
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {n : ℕ} {s : MRing (PBlk n)} {a : Unit → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : s.IsHomogeneous (a ()) := by
  intro m hm
  rw [← hs m (mem_support_iff.mpr hm) ()]
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_sigma]
end GroundTheory.Heights₂.Heights.ObjectsChow
