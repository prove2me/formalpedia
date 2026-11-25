-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_baseSubst_mem_fibreIdeal_c1ee86e42993
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:27.579379+00:00
-- url     : https://prove2.me/submissions/664f3ecb-0ee0-4193-a4d8-9fca3f3232a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreBij
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_aeval_baseSubst_c8867875a98c


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
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    baseSubst κ G f ∈ fibreIdeal κ G ↔ f ∈ P' := by
  rw [fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]
end GroundTheory.Heights₂.Heights.Inter
