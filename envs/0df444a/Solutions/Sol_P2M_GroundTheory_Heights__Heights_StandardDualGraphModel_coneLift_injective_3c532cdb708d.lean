-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_coneLift_injective_3c532cdb708d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:19:17.802861+00:00
-- url     : https://prove2.me/submissions/30bd7f03-da7e-4b92-8f6c-1ee8bd2b9ea5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdGraphModel

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualGraphModel
open StandardDualImageBottom
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.StandardDualGraphModel
theorem _root_.solution (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    Function.Injective (coneLift b) :=
  RingHom.lift_injective_of_ker_le_ideal _ _ fun _ ha => ha
end GroundTheory.Heights₂.Heights.StandardDualGraphModel
