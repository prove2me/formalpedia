-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_isUnit_baseSubst_rename_67bd4c226138
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:32.34091+00:00
-- url     : https://prove2.me/submissions/c032c6a3-11a0-4e19-82ad-152a9d37add0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_baseSubst_rename_49ffc4fb7581

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
omit [Fintype K'] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') {t : MRing ι} (ht : aeval G.x t ≠ 0) :
    IsUnit (baseSubst κ G (rename v t)) := by
  rw [baseSubst_rename hv]
  exact (isUnit_iff_ne_zero.mpr ht).map C
end GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
