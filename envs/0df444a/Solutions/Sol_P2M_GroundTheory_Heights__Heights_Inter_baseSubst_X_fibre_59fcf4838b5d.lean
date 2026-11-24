-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_baseSubst_X_fibre_59fcf4838b5d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:12.101865+00:00
-- url     : https://prove2.me/submissions/45498493-07dc-4d9f-8316-bc179ee04424

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreBij

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
theorem _root_.solution (G : GenFibre v P') (q : Σ k : FibreBlock κ, ι' k.1) :
    baseSubst κ G (X ⟨q.1.1, q.2⟩) = X q := by
  unfold baseSubst
  rw [eval₂Hom_X', dif_neg q.1.2]
end GroundTheory.Heights₂.Heights.Inter
