-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_exists_clear_d073348b32e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:10:17.326964+00:00
-- url     : https://prove2.me/submissions/7afd9fb7-40a1-4586-ae7c-2ec8eda99c12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFHoriz
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_baseSubst_rename_cb9c3ab4b8a4

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
open GroundTheory.Heights₂.Heights.Inter.PFHoriz
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
namespace GroundTheory.Heights₂.Heights.Inter.PFHoriz
theorem _root_.solution (hκv : IsBlockMap κ v) (G : GenFibre v P') (g : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (b : MRing ι) (F : MRing ι'), aeval G.x b ≠ 0 ∧ C (aeval G.x b) * g = baseSubst κ G F := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨f, b, hb, rfl⟩ := G.gen a
    refine ⟨b, rename v f, hb, ?_⟩
    rw [baseSubst_rename hκv, ← C_mul, mul_div_cancel₀ _ hb]
  | add p q hp hq =>
    obtain ⟨b₁, F₁, h₁, e₁⟩ := hp
    obtain ⟨b₂, F₂, h₂, e₂⟩ := hq
    refine ⟨b₁ * b₂, rename v b₂ * F₁ + rename v b₁ * F₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add, map_mul, baseSubst_rename hκv, ← e₁, ← e₂]
    ring
  | mul_X p n hp =>
    obtain ⟨b, F, h, e⟩ := hp
    refine ⟨b, F * X ⟨n.1.1, n.2⟩, h, ?_⟩
    rw [map_mul, ← e, mul_assoc]
    congr 2
    rw [baseSubst, eval₂Hom_X', dif_neg n.1.2]
end GroundTheory.Heights₂.Heights.Inter.PFHoriz
