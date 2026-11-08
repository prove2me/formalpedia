-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.polynomialSchedule_coeff_sizeBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:32:44.371132+00:00
-- url     : https://prove2.me/submissions/cbc4e1d7-717a-4234-9f9f-cd18334f59ca

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_24
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (A D M S K n : Nat)
    (hD : D ≤ A) (hDPositive : 0 < D) (hMPositive : 0 < M) (hn : 0 < n)
    (hSmall : 12 * M ≤ D * n ^ 2)
    (hRank : 36 * K * S ≤ 5 * D ^ 2)
    (hRectangle : 4 * S ≤ M * D * n ^ 3) :
    0 < D * n ^ 6 ∧
    D * n ^ 6 ≤ A * n ^ 6 ∧
    6 * (2 * (M * n ^ 4)) ≤ D * n ^ 6 ∧
    36 * (K * n ^ 5) * (S * n ^ 7) ≤
      5 * (D * n ^ 6) * (D * n ^ 6) ∧
    4 ≤ D * n ^ 6 ∧
    4 * (M * n ^ 4) ≤ D * n ^ 6 ∧
    4 * (S * n ^ 7) ≤ (M * n ^ 4) * (D * n ^ 6) := by
  have hN4 : 0 < n ^ 4 := Nat.pow_pos hn
  have hN6 : 0 < n ^ 6 := Nat.pow_pos hn
  have hDistancePositive : 0 < D * n ^ 6 := Nat.mul_pos hDPositive hN6
  have hLength : D * n ^ 6 ≤ A * n ^ 6 := Nat.mul_le_mul_right _ hD
  have hSmallScaled : 6 * (2 * (M * n ^ 4)) ≤ D * n ^ 6 := by
    calc
      6 * (2 * (M * n ^ 4)) = (12 * M) * n ^ 4 := by ring
      _ ≤ (D * n ^ 2) * n ^ 4 := Nat.mul_le_mul_right _ hSmall
      _ = D * n ^ 6 := by ring
  have hRankScaled :
      36 * (K * n ^ 5) * (S * n ^ 7) ≤
        5 * (D * n ^ 6) * (D * n ^ 6) := by
    calc
      36 * (K * n ^ 5) * (S * n ^ 7) =
          (36 * K * S) * n ^ 12 := by ring
      _ ≤ (5 * D ^ 2) * n ^ 12 := Nat.mul_le_mul_right _ hRank
      _ = 5 * (D * n ^ 6) * (D * n ^ 6) := by ring
  have hFour : 4 ≤ D * n ^ 6 := by
    calc
      4 ≤ 12 * (M * n ^ 4) := by nlinarith [Nat.mul_pos hMPositive hN4]
      _ = 6 * (2 * (M * n ^ 4)) := by ring
      _ ≤ D * n ^ 6 := hSmallScaled
  have hDistanceScale : 4 * (M * n ^ 4) ≤ D * n ^ 6 := by
    calc
      4 * (M * n ^ 4) ≤ 12 * (M * n ^ 4) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 6 * (2 * (M * n ^ 4)) := by ring
      _ ≤ D * n ^ 6 := hSmallScaled
  have hRectangleScale :
      4 * (S * n ^ 7) ≤ (M * n ^ 4) * (D * n ^ 6) := by
    calc
      4 * (S * n ^ 7) = (4 * S) * n ^ 7 := by ring
      _ ≤ (M * D * n ^ 3) * n ^ 7 :=
        Nat.mul_le_mul_right _ hRectangle
      _ = (M * n ^ 4) * (D * n ^ 6) := by ring
  exact ⟨hDistancePositive, hLength, hSmallScaled, hRankScaled,
    hFour, hDistanceScale, hRectangleScale⟩
end QEC.Coding.TannerLiftedProduct
