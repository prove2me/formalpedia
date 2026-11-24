-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.root_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:20.477819+00:00
-- url     : https://prove2.me/submissions/2e776be8-d9ce-4050-9db5-f9705eab82a1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_isDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (hv : v.Integers R) {n : ℕ} (hn : (n : R) ∉ mI hv) {x y : R} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hxy : x - y ∈ mI hv) : x = y := by
  have := isDomain hv
  have hgeom := (Commute.all x y).geom_sum₂_mul n
  rw [hx, hy, sub_self] at hgeom
  rcases mul_eq_zero.1 hgeom with h | h
  · exfalso
    have hres : res hv (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = (n : R ⧸ mI hv) * res hv x ^ (n - 1) := by
      have hxy' : res hv x = res hv y := by
        rw [← sub_eq_zero, ← map_sub]; exact Ideal.Quotient.eq_zero_iff_mem.2 hxy
      rw [map_sum]
      simp only [map_mul, map_pow, ← hxy']
      rw [Finset.sum_congr rfl (g := fun _ => res hv x ^ (n - 1)), Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      intro i hi
      rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hx0 : res hv x ≠ 0 := by
      intro h0; have := congrArg (res hv) hx; rw [map_pow, h0, zero_pow hn0, map_one] at this
      exact zero_ne_one this
    have hnn : (n : R ⧸ mI hv) ≠ 0 := by
      rw [← map_natCast (res hv)]; exact fun h0 => hn (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    rw [h, map_zero] at hres
    exact mul_ne_zero hnn (pow_ne_zero _ hx0) hres.symm
  · exact sub_eq_zero.1 h
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
