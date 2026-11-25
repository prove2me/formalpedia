-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_comap_fibreOf_e23ffdb2b160
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:38.496973+00:00
-- url     : https://prove2.me/submissions/4251db4b-49e3-4212-a95d-3e2b6b131807

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreBij
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_baseSubst_rename_36a1088da003
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_of_baseSubst_eq_zero_bce603bba2ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_exists_mul_eq_baseSubst_9cf196503e6a

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
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') : (fibreOf κ G W).comap (baseSubst κ G) = W := by
  refine le_antisymm (fun f hf => ?_) Ideal.le_comap_map
  have key : ∀ c ∈ fibreOf κ G W, ∃ w ∈ W, ∃ g : MRing ι, aeval G.x g ≠ 0 ∧
      c * C (aeval G.x g) = baseSubst κ G w := by
    intro c hc
    unfold fibreOf Ideal.map Ideal.span at hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨w, hw, rfl⟩ := hc
      exact ⟨w, hw, 1, by simp, by simp⟩
    | zero => exact ⟨0, W.zero_mem, 1, by simp, by simp⟩
    | add c₁ c₂ _ _ ih₁ ih₂ =>
      obtain ⟨w₁, hw₁, g₁, h₁, e₁⟩ := ih₁
      obtain ⟨w₂, hw₂, g₂, h₂, e₂⟩ := ih₂
      refine ⟨w₁ * rename v g₂ + w₂ * rename v g₁, W.add_mem (W.mul_mem_right _ hw₁) (W.mul_mem_right _ hw₂),
        g₁ * g₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
      simp only [map_add, map_mul, baseSubst_rename hv]
      rw [← e₁, ← e₂]
      ring
    | smul a c _ ih =>
      obtain ⟨w, hw, g, h, e⟩ := ih
      obtain ⟨F, g', h', e'⟩ := exists_mul_eq_baseSubst hv G a
      refine ⟨F * w, W.mul_mem_left _ hw, g' * g, by rw [map_mul]; exact mul_ne_zero h' h, ?_⟩
      simp only [smul_eq_mul, map_mul]
      rw [← e', ← e]
      ring
  obtain ⟨w, hw, g, hg, e⟩ := key _ hf
  have h0 : f * rename v g - w ∈ P' :=
    mem_of_baseSubst_eq_zero hv G (by rw [map_sub, map_mul, baseSubst_rename hv, e, sub_self])
  have h1 : f * rename v g ∈ W := by simpa using W.add_mem (hPW h0) hw
  rcases hW.mem_or_mem h1 with h | h
  · exact h
  · refine absurd ?_ hg
    have hg' : g ∈ imageZ v W := h
    rw [hI, ← G.ker_x] at hg'
    exact hg'
end GroundTheory.Heights₂.Heights.Inter
