-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_isMultiHomog_ren_f61869dec676
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:57:56.257693+00:00
-- url     : https://prove2.me/submissions/b23043df-6738-4a94-b296-61e729e6e0fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_sum_fiber_ae321566fe81
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_ren_apply_8f65176f1b12

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)
include hσ
namespace GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
theorem _root_.solution {f : MRingOver F ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    IsMultiHomog (ren σ f) (a ∘ e.symm) := by
  classical
  intro m hm k'
  rw [ren_apply, support_rename_of_injective σ.injective, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [sum_fiber, Function.comp_apply, ← h m₀ hm₀ (e.symm k'), sum_fiber]
  refine (Equiv.sum_comp σ _).symm.trans (Finset.sum_congr rfl fun p _ => ?_)
  rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply, hσ, Equiv.apply_eq_iff_eq_symm_apply]
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
