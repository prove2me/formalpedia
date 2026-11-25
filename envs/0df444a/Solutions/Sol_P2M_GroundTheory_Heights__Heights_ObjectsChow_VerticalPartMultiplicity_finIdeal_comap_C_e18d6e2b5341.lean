-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_comap_C_e18d6e2b5341
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:34.4012+00:00
-- url     : https://prove2.me/submissions/cc66a3e9-e3cc-46e3-8d9b-042bc399ef02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient

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
open GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
theorem _root_.solution (P : Ideal (MRing (PBlk n))) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).comap (C : ℤ →+* MvPolynomial (Fin n) ℤ) =
      P.comap (C : ℤ →+* MRing (PBlk n)) := by
  ext a
  simp [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, rename_C]
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
