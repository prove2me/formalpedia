-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_of_mem_map_c82db5f1edd1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:18.617595+00:00
-- url     : https://prove2.me/submissions/2818d10e-5c47-4013-85b3-448a051d96f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_baseSubst_mul_59b175cd85f0

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
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') (W : Ideal (MRing ι'))
    {g : MRingOver G.Φ (fibreIdx ι' κ)} (hg : g ∈ W.map (baseSubst κ G)) :
    ∃ (t : MRing ι) (w : MRing ι'), aeval G.x t ≠ 0 ∧ w ∈ W ∧
      baseSubst κ G (rename v t) * g = baseSubst κ G w := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨1, w, by simp, hw, by simp⟩
  | zero => exact ⟨1, 0, by simp, W.zero_mem, by simp⟩
  | add g₁ g₂ _ _ h₁ h₂ =>
    obtain ⟨t₁, w₁, ht₁, hw₁, e₁⟩ := h₁
    obtain ⟨t₂, w₂, ht₂, hw₂, e₂⟩ := h₂
    refine ⟨t₁ * t₂, w₁ * rename v t₂ + rename v t₁ * w₂, by rw [map_mul]; exact mul_ne_zero ht₁ ht₂,
      W.add_mem (W.mul_mem_right _ hw₁) (W.mul_mem_left _ hw₂), ?_⟩
    rw [map_mul, map_mul, map_add, map_mul, map_mul, ← e₁, ← e₂]
    ring
  | smul c g _ h =>
    obtain ⟨t, w, ht, hw, e⟩ := h
    obtain ⟨t', f, ht', e'⟩ := exists_baseSubst_mul hv G c
    refine ⟨t' * t, f * w, by rw [map_mul]; exact mul_ne_zero ht' ht, W.mul_mem_left _ hw, ?_⟩
    rw [smul_eq_mul, map_mul, map_mul, map_mul, ← e, ← e']
    ring
end GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
