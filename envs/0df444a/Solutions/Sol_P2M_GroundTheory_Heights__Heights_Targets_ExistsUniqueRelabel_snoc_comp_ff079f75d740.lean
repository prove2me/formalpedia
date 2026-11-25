-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_snoc_comp_ff079f75d740
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:21:09.310936+00:00
-- url     : https://prove2.me/submissions/f03649f0-109a-4c5d-9c8c-0a3943c5fd7b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



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
omit hσ
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
theorem _root_.solution {n : ℕ} (L : Fin n → K → ℤ) (A : K → ℤ) :
    (fun j => Fin.snoc (α := fun _ => K → ℤ) L A j ∘ e.symm) =
      Fin.snoc (α := fun _ => K' → ℤ) (fun j => L j ∘ e.symm) (A ∘ e.symm) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]
end GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
