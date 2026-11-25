-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_fibreOf_comap_19b9dcd15aa3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:30.867+00:00
-- url     : https://prove2.me/submissions/2a98ce2c-4c7a-4bcf-b5a9-b00d26628830

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreBij
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exists_mul_eq_baseSubst_9cf196503e6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_fibreOf_of_mul_eq_855f442f54f3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') (Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))) :
    fibreOf κ G (Q.comap (baseSubst κ G)) = Q := by
  refine le_antisymm Ideal.map_comap_le fun c hc => ?_
  obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G c
  refine mem_fibreOf_of_mul_eq G hg e ?_
  rw [Ideal.mem_comap, ← e]
  exact Q.mul_mem_right _ hc
end GroundTheory.Heights₂.Heights.Inter
