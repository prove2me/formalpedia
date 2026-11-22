-- Prove2me | solution 1 for abs_add_of_isVLDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:43.182581+00:00
-- url     : https://prove2.me/submissions/f9d92e0b-00f0-4682-9a4a-4a00dd1f92fb

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_inf_le_inf_add_inf_of_nonneg
public import Theorems.Thm_uniqueness_posPart

section
@[expose] public section
open scoped Topology
open Filter Finset
section LatticeOrdered
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
omit [IsOrderedAddMonoid X] in
private theorem inf_eq_zero_of_le_disjoint {a b c d : X}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d)
    (hcd : c ⊓ d = 0) : a ⊓ b = 0 :=
  le_antisymm (hcd ▸ inf_le_inf hac hbd) (le_inf ha hb)
end LatticeOrdered
section VectorLattice
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
end VectorLattice
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
theorem _root_.solution {x y : X} (h : IsVLDisjoint x y) :
    |x + y| = |x| + |y| := by
  have hd : |x| ⊓ |y| = 0 := h
  have hxp_yp : x⁺ ⊓ y⁺ = 0 := inf_eq_zero_of_le_disjoint
    (posPart_nonneg x) (posPart_nonneg y)
    (sup_le (le_abs_self x) (abs_nonneg x))
    (sup_le (le_abs_self y) (abs_nonneg y)) hd
  have hxp_yn : x⁺ ⊓ y⁻ = 0 := inf_eq_zero_of_le_disjoint
    (posPart_nonneg x) (negPart_nonneg y)
    (sup_le (le_abs_self x) (abs_nonneg x))
    (sup_le (neg_le_abs y) (abs_nonneg y)) hd
  have hxn_yp : x⁻ ⊓ y⁺ = 0 := inf_eq_zero_of_le_disjoint
    (negPart_nonneg x) (posPart_nonneg y)
    (sup_le (neg_le_abs x) (abs_nonneg x))
    (sup_le (le_abs_self y) (abs_nonneg y)) hd
  have hxn_yn : x⁻ ⊓ y⁻ = 0 := inf_eq_zero_of_le_disjoint
    (negPart_nonneg x) (negPart_nonneg y)
    (sup_le (neg_le_abs x) (abs_nonneg x))
    (sup_le (neg_le_abs y) (abs_nonneg y)) hd
  have hxn_xp : x⁻ ⊓ x⁺ = 0 := by
    rw [inf_comm]; exact posPart_inf_negPart_eq_zero x
  have hyn_yp : y⁻ ⊓ y⁺ = 0 := by
    rw [inf_comm]; exact posPart_inf_negPart_eq_zero y
  have term1 : (x⁺ + y⁺) ⊓ x⁻ = 0 := by
    apply le_antisymm _ (le_inf (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (negPart_nonneg x))
    rw [inf_comm]
    calc x⁻ ⊓ (x⁺ + y⁺)
        ≤ x⁻ ⊓ x⁺ + x⁻ ⊓ y⁺ := inf_le_inf_add_inf_of_nonneg x⁻ x⁺ y⁺
            (negPart_nonneg x) (posPart_nonneg x) (posPart_nonneg y)
      _ = 0 := by rw [hxn_xp, hxn_yp, add_zero]
  have term2 : (x⁺ + y⁺) ⊓ y⁻ = 0 := by
    apply le_antisymm _ (le_inf (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (negPart_nonneg y))
    rw [inf_comm]
    calc y⁻ ⊓ (x⁺ + y⁺)
        ≤ y⁻ ⊓ x⁺ + y⁻ ⊓ y⁺ := inf_le_inf_add_inf_of_nonneg y⁻ x⁺ y⁺
            (negPart_nonneg y) (posPart_nonneg x) (posPart_nonneg y)
      _ = 0 := by rw [inf_comm y⁻ x⁺, hxp_yn, hyn_yp, add_zero]
  have sum_disj : (x⁺ + y⁺) ⊓ (x⁻ + y⁻) = 0 := by
    apply le_antisymm _ (le_inf (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
      (add_nonneg (negPart_nonneg x) (negPart_nonneg y)))
    calc (x⁺ + y⁺) ⊓ (x⁻ + y⁻)
        ≤ (x⁺ + y⁺) ⊓ x⁻ + (x⁺ + y⁺) ⊓ y⁻ :=
          inf_le_inf_add_inf_of_nonneg (x⁺ + y⁺) x⁻ y⁻
            (add_nonneg (posPart_nonneg x) (posPart_nonneg y))
            (negPart_nonneg x) (negPart_nonneg y)
      _ = 0 := by rw [term1, term2, add_zero]
  have hdec : x + y = (x⁺ + y⁺) - (x⁻ + y⁻) := by
    calc x + y = (x⁺ - x⁻) + (y⁺ - y⁻) := by
          rw [posPart_sub_negPart, posPart_sub_negPart]
      _ = (x⁺ + y⁺) - (x⁻ + y⁻) := by abel
  have hup := uniqueness_posPart (x + y) hdec sum_disj
  have hun : (x + y)⁻ = x⁻ + y⁻ := by
    have h3 := posPart_sub_negPart (x + y)
    rw [← hup] at h3
    have h4 : x⁺ + y⁺ - (x + y)⁻ = x⁺ + y⁺ - (x⁻ + y⁻) := by
      rw [h3, hdec]
    exact sub_right_injective h4
  calc |x + y| = (x + y)⁺ + (x + y)⁻ := (posPart_add_negPart (x + y)).symm
    _ = (x⁺ + y⁺) + (x⁻ + y⁻) := by rw [← hup, hun]
    _ = (x⁺ + x⁻) + (y⁺ + y⁻) := by abel
    _ = |x| + |y| := by rw [posPart_add_negPart, posPart_add_negPart]
