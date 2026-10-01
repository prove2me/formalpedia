-- Prove2me | solution 1 for SteinitzExchange.Extension.toReal_mem_hull_iff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @choi
-- created : 2026-10-01T03:47:03.157996+00:00
-- url     : https://prove2.me/submissions/65a455ec-9867-48e5-b5dc-449d6eb1d9fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_SetFunction
import Theorems.Thm_SteinitzExchange_Duality_baseSet_iff_submodular_system

open SteinitzExchange.Extension

/-- Eq. (2.3) follows from the subset-sum description in Theorem 2.1: all defining real
halfspaces and the total-sum hyperplane contain the convex hull, and an integer point satisfying
these constraints belongs to the original base set. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (x : V → ℤ) :
    toReal x ∈ hull B ↔ x ∈ B := by
  classical
  constructor
  · intro hx
    have hBD : SteinitzExchange.Duality.IsIntegralBaseSet B := by
      simpa only [IsIntegralBaseSet, chi,
        SteinitzExchange.Duality.IsIntegralBaseSet, SteinitzExchange.Duality.chi] using hB
    obtain ⟨f, _hfsub, _hfempty, hfmem⟩ :=
      (SteinitzExchange.Duality.baseSet_iff_submodular_system B hB.1).1.mp hBD
    have hsum (X : Finset V) (y z : V → ℝ) (a b : ℝ) :
        (∑ v ∈ X, (a • y + b • z) v) =
          a * (∑ v ∈ X, y v) + b * (∑ v ∈ X, z v) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum]
    have hconv_le (X : Finset V) :
        Convex ℝ {y : V → ℝ | (∑ v ∈ X, y v) ≤ (f X : ℝ)} := by
      intro y hy z hz a b ha hb hab
      change (∑ v ∈ X, (a • y + b • z) v) ≤ (f X : ℝ)
      rw [hsum]
      calc
        a * (∑ v ∈ X, y v) + b * (∑ v ∈ X, z v) ≤
            a * (f X : ℝ) + b * (f X : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hy ha) (mul_le_mul_of_nonneg_left hz hb)
        _ = (f X : ℝ) := by rw [← add_mul, hab, one_mul]
    have hxle (X : Finset V) : (∑ v ∈ X, toReal x v) ≤ (f X : ℝ) := by
      apply convexHull_min (s := toReal '' (B : Set (V → ℤ))) ?_ (hconv_le X) hx
      rintro _ ⟨z, hz, rfl⟩
      have hzle := ((hfmem z).mp hz).1 X
      change (∑ v ∈ X, (z v : ℝ)) ≤ (f X : ℝ)
      change (∑ v ∈ X, z v) ≤ f X at hzle
      exact_mod_cast hzle
    have hconv_eq : Convex ℝ
        {y : V → ℝ | (∑ v, y v) = (f Finset.univ : ℝ)} := by
      intro y hy z hz a b _ha _hb hab
      change (∑ v, (a • y + b • z) v) = (f Finset.univ : ℝ)
      rw [hsum Finset.univ, hy, hz, ← add_mul, hab, one_mul]
    have hxeq : (∑ v, toReal x v) = (f Finset.univ : ℝ) := by
      apply convexHull_min (s := toReal '' (B : Set (V → ℤ))) ?_ hconv_eq hx
      rintro _ ⟨z, hz, rfl⟩
      have hzeq := ((hfmem z).mp hz).2
      change (∑ v, (z v : ℝ)) = (f Finset.univ : ℝ)
      change (∑ v, z v) = f Finset.univ at hzeq
      exact_mod_cast hzeq
    apply (hfmem x).mpr
    constructor
    · intro X
      have hxleX := hxle X
      change (∑ v ∈ X, (x v : ℝ)) ≤ (f X : ℝ) at hxleX
      change (∑ v ∈ X, x v) ≤ f X
      exact_mod_cast hxleX
    · change (∑ v, (x v : ℝ)) = (f Finset.univ : ℝ) at hxeq
      change (∑ v, x v) = f Finset.univ
      exact_mod_cast hxeq
  · intro hx
    exact subset_convexHull ℝ _ ⟨x, hx, rfl⟩
