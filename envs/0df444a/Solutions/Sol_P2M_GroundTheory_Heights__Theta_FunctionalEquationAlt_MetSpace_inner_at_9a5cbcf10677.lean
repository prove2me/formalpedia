-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_MetSpace_inner_at_9a5cbcf10677
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:12:59.839838+00:00
-- url     : https://prove2.me/submissions/c4ae55d3-ef67-460e-8d58-45240f03eda5

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
open CAt
attribute [instance] MetSpace.instAddCommGroup MetSpace.instModule MetSpace.instFD
  MetSpace.instModuleO MetSpace.instTower
variable {E : Type} [Field E] [NumberField E]
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.MetSpace
variable (S : MetSpace E)
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.MetSpace
theorem _root_.solution (τ : InfinitePlace E) (v w : S.V) :
    inner ℂ (S.pt τ v) (S.pt τ w) =
      (S.form τ).inner ((1 : CAt τ.embedding) ⊗ₜ[E] v) ((1 : CAt τ.embedding) ⊗ₜ[E] w) := rfl
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.MetSpace
