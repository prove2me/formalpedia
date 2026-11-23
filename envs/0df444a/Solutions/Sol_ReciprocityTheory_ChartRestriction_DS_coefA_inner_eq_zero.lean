-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefA_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:39.043156+00:00
-- url     : https://prove2.me/submissions/d80d999c-ad93-466a-b38d-ca6626ccf7d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {u v : X} {α β : ℝ} (hu : T u = (α : ℂ) • u) (hv : T v = (β : ℂ) • v) (hne : α ≠ β) :
    inner ℂ u v = 0 := by
  have h := hT u v
  rw [hu, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have hne' : (α : ℂ) - β ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have h0 : ((α : ℂ) - β) * inner ℂ u v = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left hne'
end ReciprocityTheory.ChartRestriction.DS
