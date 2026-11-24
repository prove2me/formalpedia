-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_exists_mul_eq_baseSubst_9cf196503e6a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:12.119396+00:00
-- url     : https://prove2.me/submissions/72ae3ace-cae6-4c46-b5f7-97db3953a276

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreBij
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_baseSubst_rename_36a1088da003
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_baseSubst_X_fibre_59fcf4838b5d

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
theorem _root_.solution (hv : IsBlockMap κ v) (G : GenFibre v P') (c : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (F : MRing ι') (g : MRing ι), aeval G.x g ≠ 0 ∧ c * C (aeval G.x g) = baseSubst κ G F := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨f, g, hg, rfl⟩ := G.gen a
    refine ⟨rename v f, g, hg, ?_⟩
    rw [baseSubst_rename hv, ← C_mul, div_mul_cancel₀ _ hg]
  | add c₁ c₂ ih₁ ih₂ =>
    obtain ⟨F₁, g₁, h₁, e₁⟩ := ih₁
    obtain ⟨F₂, g₂, h₂, e₂⟩ := ih₂
    refine ⟨F₁ * rename v g₂ + F₂ * rename v g₁, g₁ * g₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add, map_mul, baseSubst_rename hv]
    rw [← e₁, ← e₂]
    ring
  | mul_X c q ih =>
    obtain ⟨F, g, hg, e⟩ := ih
    refine ⟨F * X ⟨q.1.1, q.2⟩, g, hg, ?_⟩
    rw [map_mul, ← e, baseSubst_X_fibre]
    ring
end GroundTheory.Heights₂.Heights.Inter
