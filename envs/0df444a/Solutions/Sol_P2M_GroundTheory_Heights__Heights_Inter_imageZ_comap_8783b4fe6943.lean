-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_imageZ_comap_8783b4fe6943
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:35.337918+00:00
-- url     : https://prove2.me/submissions/6589e07a-0c0a-4690-ab20-3d7c44df4ac3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreBij
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_baseSubst_rename_36a1088da003

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
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') {Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))}
    (hQ : Q ≠ ⊤) : imageZ v (Q.comap (baseSubst κ G)) = imageZ v P' := by
  ext g
  rw [← G.ker_x, RingHom.mem_ker, imageZ, Ideal.mem_comap, Ideal.mem_comap]
  show baseSubst κ G (rename v g) ∈ Q ↔ _
  rw [baseSubst_rename hv]
  constructor
  · intro h
    by_contra hne
    exact hQ (Q.eq_top_of_isUnit_mem h ((isUnit_iff_ne_zero.mpr hne).map C))
  · intro h
    rw [h, map_zero]
    exact Q.zero_mem
end GroundTheory.Heights₂.Heights.Inter
