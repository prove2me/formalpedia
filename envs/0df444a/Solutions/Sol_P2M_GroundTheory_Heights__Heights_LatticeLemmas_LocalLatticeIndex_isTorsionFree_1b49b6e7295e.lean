-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_isTorsionFree_1b49b6e7295e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:02.935805+00:00
-- url     : https://prove2.me/submissions/72aae9ea-2735-4bb9-b5b3-1d6a31044633

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalLatticeIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  {E : Type*} [AddCommGroup E] [Module (v.adicCompletion K) E]
  [Module (v.adicCompletionIntegers K) E]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) E]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace LocalLatticeIndex
theorem _root_.solution (A : Submodule (v.adicCompletionIntegers K) E) :
    Module.IsTorsionFree (v.adicCompletionIntegers K) A := by
  refine .of_smul_eq_zero fun r x h => ?_
  have h' : algebraMap _ (v.adicCompletion K) r • (x : E) = 0 := by
    rw [algebraMap_smul, ← Submodule.coe_smul, h, Submodule.coe_zero]
  rcases smul_eq_zero.1 h' with hr | hx
  · exact Or.inl ((FaithfulSMul.algebraMap_injective _ (v.adicCompletion K)).eq_iff' (map_zero _) |>.1 hr)
  · exact Or.inr (Subtype.ext hx)
end LocalLatticeIndex
end GroundTheory.Heights₂.Heights.LatticeLemmas
