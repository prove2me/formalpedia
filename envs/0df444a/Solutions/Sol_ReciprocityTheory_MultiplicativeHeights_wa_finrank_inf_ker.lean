-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_finrank_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:51.434058+00:00
-- url     : https://prove2.me/submissions/21a2ac5c-e73d-46d0-a6a7-c2c2f5350090

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (f : V →ₗ[K] K) (z : V) (hz : z ∈ W)
    (hfz : f z ≠ 0) : finrank K ↥(W ⊓ LinearMap.ker f) + 1 = finrank K W := by
  have hsup : W ⊔ LinearMap.ker f = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = (f v / f z) • z + (v - (f v / f z) • z) := by abel
    rw [hv]
    refine Submodule.add_mem_sup (W.smul_mem _ hz) ?_
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfz, sub_self]
  have hker : finrank K (LinearMap.ker f) + 1 = finrank K V := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    have hr : LinearMap.range f = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact ⟨(a / f z) • z, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfz]⟩
    rw [hr, finrank_top, Module.finrank_self] at h
    omega
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  rw [hsup, finrank_top] at h
  omega
end ReciprocityTheory.MultiplicativeHeights
