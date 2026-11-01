-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_arithmetic__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:05:42.353131+00:00
-- url     : https://prove2.me/submissions/276bef97-b3e4-4e37-a744-ef5a30bc0ae8

import Mathlib

set_option autoImplicit false

theorem solution
    {F : Type} [Fintype F]
    (n e : ℕ) (length : F → ℕ)
    (hn : 3 ≤ n)
    (hEuler : (n : ℤ) - (e : ℤ) + (Fintype.card F : ℤ) = 2)
    (hIncidence : (∑ f : F, (length f : ℤ)) = 2 * (e : ℤ))
    (hTriangular : (∑ f : F, (length f : ℤ)) = 3 * (Fintype.card F : ℤ)) :
    e = 3 * n - 6 := by
  have hFaces : 2 * (e : ℤ) = 3 * (Fintype.card F : ℤ) := by
    omega
  have hInt : (e : ℤ) = 3 * (n : ℤ) - 6 := by
    omega
  have hLower : 6 ≤ 3 * n := by
    omega
  have hCast : ((3 * n - 6 : ℕ) : ℤ) = 3 * (n : ℤ) - 6 := by
    rw [Nat.cast_sub hLower]
    norm_num
  have hCastEq : (e : ℤ) = ((3 * n - 6 : ℕ) : ℤ) := by
    exact hInt.trans hCast.symm
  exact_mod_cast hCastEq