-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecStabGroup_le_vecFixGroup_03fa43eba001
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:06.465718+00:00
-- url     : https://prove2.me/submissions/c877dcce-3669-4020-9893-def31e47384c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldingTorus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldAlongSubgroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHaarParabolicCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldingTorus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_smul_vecAt_b12bc12835a1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
    (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W) (x₀ : W) :
    vecStabGroup h v La x₀ ≤ vecFixGroup h v x₀ := by
  rintro _ ⟨γ, hγ, rfl⟩
  have e := archEmbed_smul_vecAt h v (γ : h.unitaryGroup) x₀
  rw [show (γ : h.unitaryGroup) • x₀ = x₀ from MulAction.mem_stabilizer_iff.1 hγ] at e
  exact fun w => congrFun e w
end GroundTheory.Heights₂.Heights.FiniteCovolume
