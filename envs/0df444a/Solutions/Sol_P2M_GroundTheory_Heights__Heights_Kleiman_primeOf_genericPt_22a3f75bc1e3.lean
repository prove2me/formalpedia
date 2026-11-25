-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_primeOf_genericPt_22a3f75bc1e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:19.638107+00:00
-- url     : https://prove2.me/submissions/5e3354bf-f45a-47b3-b657-ca9cb5358c3a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_aeval_genericPt_77930e4eb734

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable (k : Type u) [Field k] (N : ℕ)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : primeOf (S := k) (genericPt k N) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  have hc : ∀ d, homogeneousComponent d f = 0 := by
    intro d
    have h1 := homogeneousComponent_mem_primeOf _ hf d
    rw [mem_primeOf_of_isHomogeneous _ (homogeneousComponent_isHomogeneous d f),
      aeval_genericPt] at h1
    exact (map_eq_zero_iff _ (IsFractionRing.injective (Poly k N) (FractionRing (Poly k N)))).mp h1
  rw [← sum_homogeneousComponent f]
  exact Finset.sum_eq_zero fun d _ => hc d
end GroundTheory.Heights₂.Heights.Kleiman
