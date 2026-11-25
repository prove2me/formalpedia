-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectiveArithmeticVariety_coord_eq_6fdaee643af6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:48.114875+00:00
-- url     : https://prove2.me/submissions/93ff2e87-f89f-43e4-9546-36980c12eac6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjArithVar

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety
variable (K : Type) [Field K] [NumberField K] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety
theorem _root_.solution (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (j : Fin (n + 1)) :
    projSpaceCoord K (n + 1) ⟨(), (m, j)⟩ =
      algebraMap K (ProjField K (n + 1)) (integralBasis K m) * xc K n j := by
  simp only [projSpaceCoord, map_mul, xc]
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
end GroundTheory.Heights₂.Heights.ProjectiveArithmeticVariety
