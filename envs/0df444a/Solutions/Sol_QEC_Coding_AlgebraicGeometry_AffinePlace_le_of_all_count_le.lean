-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.le_of_all_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:12:21.76857+00:00
-- url     : https://prove2.me/submissions/843488db-c87a-43c9-8500-90b60b9c2073

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero nonZeroDivisors
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_45ffe40864_30
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution {I J : affineFractionalIdeal k F}
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (hcount : ∀ P : carrier k F,
      FractionalIdeal.count F P J ≤ FractionalIdeal.count F P I) :
    I ≤ J := by
  classical
  let B : Type _ := affineRing k F
  let D : FractionalIdeal B⁰ F := I * J⁻¹
  have hD : D ≠ 0 := by
    dsimp [D]
    exact mul_ne_zero hI (inv_ne_zero hJ)
  have hDcount (P : carrier k F) :
      FractionalIdeal.count F P D =
        FractionalIdeal.count F P I - FractionalIdeal.count F P J := by
    dsimp [D]
    rw [FractionalIdeal.count_mul F P hI (inv_ne_zero hJ),
      FractionalIdeal.count_inv]
    ring
  have hDnonneg (P : carrier k F) : 0 ≤ FractionalIdeal.count F P D := by
    rw [hDcount]
    exact sub_nonneg.mpr (hcount P)
  let H : Ideal B := ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum B,
    P.asIdeal ^ Int.toNat (FractionalIdeal.count F P D)
  have hH : (H : FractionalIdeal B⁰ F) = D := by
    calc
      (H : FractionalIdeal B⁰ F) = ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum B,
          (P.asIdeal : FractionalIdeal B⁰ F) ^
            Int.toNat (FractionalIdeal.count F P D) := by
        dsimp [H]
        rw [FractionalIdeal.coeIdeal_finprod B⁰ F (le_refl _)]
        apply finprod_congr
        intro P
        exact FractionalIdeal.coeIdeal_pow (S := B⁰) (P := F) P.asIdeal
          (Int.toNat (FractionalIdeal.count F P D))
      _ = ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum B,
          (P.asIdeal : FractionalIdeal B⁰ F) ^ FractionalIdeal.count F P D := by
        apply finprod_congr
        intro P
        conv_rhs => rw [← Int.toNat_of_nonneg (hDnonneg P), zpow_natCast]
      _ = D := FractionalIdeal.finprod_heightOneSpectrum_factorization'
        (R := B) (K := F) hD
  have hDle : D ≤ (1 : FractionalIdeal B⁰ F) := by
    rw [← hH]
    exact FractionalIdeal.coeIdeal_le_one
  have hIeq : I = D * J := by
    calc
      I = I * 1 := (mul_one I).symm
      _ = I * (J⁻¹ * J) := by rw [inv_mul_cancel₀ hJ]
      _ = (I * J⁻¹) * J := (mul_assoc I J⁻¹ J).symm
      _ = D * J := rfl
  calc
    I = D * J := hIeq
    _ ≤ 1 * J := mul_le_mul_left hDle J
    _ = J := one_mul J
end QEC.Coding.AlgebraicGeometry.AffinePlace
