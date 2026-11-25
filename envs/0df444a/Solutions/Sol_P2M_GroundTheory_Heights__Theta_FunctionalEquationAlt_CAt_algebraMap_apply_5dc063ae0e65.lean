-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_CAt_algebraMap_apply_5dc063ae0e65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:22.617994+00:00
-- url     : https://prove2.me/submissions/576db733-cbfd-46c0-a854-9e1871aa2d27

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ChainWittIndexHypothesesMet
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_MemRangeIffIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open NumberField TensorProduct Module GroundTheory.Automorphic
open scoped nonZeroDivisors
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.CAt
variable {E : Type} [Field E] (σ : E →+* ℂ)
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.CAt
theorem _root_.solution (a : E) : algebraMap E (CAt σ) a = ofComplex σ (σ a) := rfl
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.CAt
