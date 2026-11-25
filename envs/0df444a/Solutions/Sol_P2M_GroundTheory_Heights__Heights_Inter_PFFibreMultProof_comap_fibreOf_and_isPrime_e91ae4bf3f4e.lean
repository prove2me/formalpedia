-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_comap_fibreOf_and_isPrime_e91ae4bf3f4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:13:50.276343+00:00
-- url     : https://prove2.me/submissions/3fcf5272-0181-4a06-ac99-78bc8f9f1ab8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_baseSubst_mul_59b175cd85f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_isUnit_baseSubst_rename_67bd4c226138
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_ker_baseSubst_le_237afa69f022
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_of_mem_map_c82db5f1edd1

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
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime]
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') :
    (fibreOf κ G W).comap (baseSubst κ G) = W ∧ (fibreOf κ G W).IsPrime := by
  have htW : ∀ t : MRing ι, aeval G.x t ≠ 0 → rename v t ∉ W := by
    intro t ht h
    have h' : t ∈ imageZ v W := h
    rw [hI, ← G.ker_x, RingHom.mem_ker] at h'
    exact ht h'
  have hc : (fibreOf κ G W).comap (baseSubst κ G) = W := by
    refine le_antisymm (fun a ha => ?_) Ideal.le_comap_map
    obtain ⟨t, w, ht, hw, e⟩ := exists_of_mem_map hv G W ha
    have hk : rename v t * a - w ∈ W := by
      apply hPW
      apply ker_baseSubst_le hv G
      rw [RingHom.mem_ker, map_sub, map_mul, e, sub_self]
    have hta : rename v t * a ∈ W := by simpa using W.add_mem hk hw
    exact ((Ideal.IsPrime.mem_or_mem ‹_› hta).resolve_left (htW t ht))
  refine ⟨hc, Ideal.isPrime_iff.mpr ⟨fun h => ?_, fun {g₁ g₂} h => ?_⟩⟩
  · have h1 : (1 : MRing ι') ∈ W := by
      rw [← hc, Ideal.mem_comap, map_one, h]
      exact Submodule.mem_top
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one W).mpr h1)
  · obtain ⟨t₁, f₁, ht₁, e₁⟩ := exists_baseSubst_mul hv G g₁
    obtain ⟨t₂, f₂, ht₂, e₂⟩ := exists_baseSubst_mul hv G g₂
    have hf : f₁ * f₂ ∈ W := by
      rw [← hc, Ideal.mem_comap, map_mul, ← e₁, ← e₂,
        show baseSubst κ G (rename v t₁) * g₁ * (baseSubst κ G (rename v t₂) * g₂) =
          baseSubst κ G (rename v t₁) * baseSubst κ G (rename v t₂) * (g₁ * g₂) by ring]
      exact Ideal.mul_mem_left _ _ h
    rcases Ideal.IsPrime.mem_or_mem ‹_› hf with hf | hf
    · left
      rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht₁), e₁, ← Ideal.mem_comap, hc]
      exact hf
    · right
      rw [← Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht₂), e₂, ← Ideal.mem_comap, hc]
      exact hf
end GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
