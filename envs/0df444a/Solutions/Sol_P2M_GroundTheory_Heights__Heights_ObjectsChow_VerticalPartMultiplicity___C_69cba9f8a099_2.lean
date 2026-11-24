-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___C_69cba9f8a099
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:50.260319+00:00
-- url     : https://prove2.me/submissions/cbdae110-6692-4657-850e-5c55c376c83e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___apply_a3d15408a314

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
theorem _root_.solution (a : ℤ) : Ψ n (C a) = C (ι a) := by
  rw [Ψ_apply, rename_C, map_C]
  rfl
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
