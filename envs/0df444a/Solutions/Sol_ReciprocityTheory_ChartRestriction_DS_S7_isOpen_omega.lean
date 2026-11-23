-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.isOpen_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:10:05.576845+00:00
-- url     : https://prove2.me/submissions/fbeb85f1-e772-4bf1-b5c2-f0f47ec5ab76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_Minors
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private lemma lead_differentiable_lemma (i : ℕ) :
    Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by
  have hent : ∀ a b : Fin n, Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
    intro a b
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => M a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).differentiable
  unfold lead
  split_ifs with h
  · simp only [Matrix.det_apply', Matrix.submatrix_apply]
    fun_prop
  · exact differentiable_const _
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution : IsOpen (OmegaSet n) := by
  have : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (lead_differentiable_lemma _).continuous continuous_const
end ReciprocityTheory.ChartRestriction.DS.S7
