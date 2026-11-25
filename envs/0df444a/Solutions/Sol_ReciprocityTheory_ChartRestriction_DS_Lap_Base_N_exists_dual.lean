-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:54.196377+00:00
-- url     : https://prove2.me/submissions/c9e0b681-69ab-493f-8e87-0f548013e7a6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExistsCyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution {m : ℕ} (x c : Fin m → ℝ) (hx : Function.Injective x) (hc : ∀ s, c s ≠ 0)
    (y : Fin m → ℝ) : ∃ v : Fin m → ℝ, ∀ i : Fin m, formV v (fun s => x s ^ i.val * c s) = y i := by
  classical
  have hW : IsUnit (Matrix.vandermonde x)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.det_vandermonde_ne_zero_iff.2 hx).isUnit
  refine ⟨fun s => ((Matrix.vandermonde x)ᵀ⁻¹ *ᵥ y) s / ((-1) ^ (s.val + 1) * c s), fun i => ?_⟩
  have hw : (Matrix.vandermonde x)ᵀ *ᵥ ((Matrix.vandermonde x)ᵀ⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hW, Matrix.one_mulVec]
  conv_rhs => rw [← hw]
  simp only [formV, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h1 : ((-1 : ℝ) ^ (s.val + 1) * c s) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (hc s)
  have h2 := hc s
  first
  | (field_simp; done)
  | (field_simp; ring)
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
