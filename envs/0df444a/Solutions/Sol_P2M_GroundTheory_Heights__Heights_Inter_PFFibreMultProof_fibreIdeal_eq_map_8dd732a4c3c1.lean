-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_fibreIdeal_eq_map_8dd732a4c3c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:21.385564+00:00
-- url     : https://prove2.me/submissions/5ebc320f-8a17-49b3-a377-f607bc26f1b0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_baseSubst_mul_59b175cd85f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_isUnit_baseSubst_rename_67bd4c226138
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
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') :
    fibreIdeal κ G = P'.map (baseSubst κ G) := by
  apply le_antisymm
  · intro g hg
    rw [fibreIdeal, RingHom.mem_ker] at hg
    obtain ⟨t, f, ht, e⟩ := exists_baseSubst_mul hv G g
    have hf : f ∈ P' := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker, ← aeval_baseSubst hv, ← e, map_mul, hg, mul_zero]
    rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht), e]
    exact Ideal.mem_map_of_mem _ hf
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]
    exact ha
end GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
