-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_ker_baseSubst_le_237afa69f022
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:46.073058+00:00
-- url     : https://prove2.me/submissions/e503e985-9b2f-4423-be09-749e6c4dfefc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreMult
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
omit [Fintype K'] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') : RingHom.ker (baseSubst κ G) ≤ P' := by
  intro a ha
  rw [RingHom.mem_ker] at ha
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← aeval_baseSubst hv, ha, map_zero]
end GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
