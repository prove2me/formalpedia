-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_modelMap_injective_70433ddf4f8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:25.354376+00:00
-- url     : https://prove2.me/submissions/11665130-8849-41fc-8572-3a5a65decd8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdGraphModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualGraphModel_coneLift_injective_3c532cdb708d

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
    Function.Injective (modelMap b) :=
  (IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) (dualStdModelField K i)).comp
    (MvPolynomial.map_injective _ (coneLift_injective b))
end GroundTheory.Heights₂.Heights.StandardDualGraphModel
