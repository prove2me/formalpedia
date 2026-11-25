-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_apply_6c33936e53d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:56:30.978849+00:00
-- url     : https://prove2.me/submissions/987f62f8-7b66-49a8-89c2-ae4b6c9323c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementArchCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StArchCovolumeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordEmbedBasis
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsZsmulMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementArchCocompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementArchCocompact
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementArchCocompact
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W)
    (Y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    projAt h v x₀ w₀ Y w = Y w - (star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v x₀ w -
      (star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ Y w)) • vecAt v w₀ w := rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume.ComplementArchCocompact
