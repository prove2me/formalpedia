-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_fibreOf_isPrime_58b6c2597eab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:35.064608+00:00
-- url     : https://prove2.me/submissions/8ac858c4-37b0-4da8-aa3b-25598fe0c9f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreBij
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exists_mul_eq_baseSubst_9cf196503e6a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_fibreOf_of_mul_eq_855f442f54f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_comap_fibreOf_e23ffdb2b160

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
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') {W : Ideal (MRing ι')} (hW : W.IsPrime)
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') : (fibreOf κ G W).IsPrime := by
  have hc := comap_fibreOf hv G hW hPW hI
  refine ⟨fun h => hW.ne_top ?_, fun {a b} hab => ?_⟩
  · rw [← hc, h, Ideal.comap_top]
  · obtain ⟨F, g, hg, e⟩ := exists_mul_eq_baseSubst hv G a
    obtain ⟨H, g', hg', e'⟩ := exists_mul_eq_baseSubst hv G b
    have hFH : F * H ∈ W := by
      rw [← hc, Ideal.mem_comap, map_mul, ← e, ← e']
      have : a * C (aeval G.x g) * (b * C (aeval G.x g')) = a * b * (C (aeval G.x g) * C (aeval G.x g')) := by
        ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hab
    rcases hW.mem_or_mem hFH with h | h
    · exact Or.inl (mem_fibreOf_of_mul_eq G hg e h)
    · exact Or.inr (mem_fibreOf_of_mul_eq G hg' e' h)
end GroundTheory.Heights₂.Heights.Inter
