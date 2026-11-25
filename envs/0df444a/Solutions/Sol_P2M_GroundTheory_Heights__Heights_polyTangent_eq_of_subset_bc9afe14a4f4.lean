-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_polyTangent_eq_of_subset_bc9afe14a4f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:22.319666+00:00
-- url     : https://prove2.me/submissions/83d631d2-ac7d-48b7-a70b-5d63df53b990

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_polyTangent_iff_5cba4303f0be

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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (S T : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hST : S ⊆ T) (h : ∀ f ∈ T, polyDiff p f ∈ Submodule.span ℂ (polyDiff p '' S)) :
    polyTangent S p = polyTangent T p := by
  ext v
  rw [mem_polyTangent_iff, mem_polyTangent_iff]
  refine ⟨fun hv f hf => ?_, fun hv f hf => hv f (hST hf)⟩
  have hle : Submodule.span ℂ (polyDiff p '' S) ≤ LinearMap.ker (dotForm.flip v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
    exact hv g hg
  have := hle (h f hf)
  simpa only [LinearMap.mem_ker, LinearMap.flip_apply] using this
end GroundTheory.Heights₂.Heights
