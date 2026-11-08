-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rootSchedule_coeff_sizeBounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:32:46.167283+00:00
-- url     : https://prove2.me/submissions/a995f8a0-b4be-49b5-9b12-859540ba7a02

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
    (A D M S K N x : Nat)
    (hD : D ≤ A) (hDPositive : 0 < D) (hMPositive : 0 < M)
    (hx : 0 < x) (hLower : x ^ 6 ≤ N)
    (hSmall : 12 * M ≤ D * x ^ 2)
    (hRank : 36 * K * S ≤ 5 * D ^ 2)
    (hRectangle : 4 * S ≤ M * D * x ^ 3) :
    0 < D * N ∧
    D * N ≤ A * N ∧
    6 * (2 * (M * x ^ 4)) ≤ D * N ∧
    36 * (K * x ^ 5) * (S * x ^ 7) ≤ 5 * (D * N) * (D * N) ∧
    4 ≤ D * N ∧
    4 * (M * x ^ 4) ≤ D * N ∧
    4 * (S * x ^ 7) ≤ (M * x ^ 4) * (D * N) := by
  have hNPositive : 0 < N := (Nat.pow_pos hx).trans_le hLower
  have hDistancePositive : 0 < D * N := Nat.mul_pos hDPositive hNPositive
  have hLength : D * N ≤ A * N := Nat.mul_le_mul_right N hD
  have hSmallScaled : 6 * (2 * (M * x ^ 4)) ≤ D * N := by
    calc
      6 * (2 * (M * x ^ 4)) = (12 * M) * x ^ 4 := by ring
      _ ≤ (D * x ^ 2) * x ^ 4 := Nat.mul_le_mul_right _ hSmall
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hLower
  have hLowerSquare : x ^ 12 ≤ N ^ 2 := by
    calc
      x ^ 12 = (x ^ 6) ^ 2 := by ring
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hLower 2
  have hRankScaled :
      36 * (K * x ^ 5) * (S * x ^ 7) ≤ 5 * (D * N) * (D * N) := by
    calc
      36 * (K * x ^ 5) * (S * x ^ 7) =
          (36 * K * S) * x ^ 12 := by ring
      _ ≤ (5 * D ^ 2) * x ^ 12 := Nat.mul_le_mul_right _ hRank
      _ ≤ (5 * D ^ 2) * N ^ 2 :=
        Nat.mul_le_mul_left (5 * D ^ 2) hLowerSquare
      _ = 5 * (D * N) * (D * N) := by ring
  have hMX4 : 0 < M * x ^ 4 :=
    Nat.mul_pos hMPositive (Nat.pow_pos hx)
  have hFour : 4 ≤ D * N := by
    calc
      4 ≤ 12 * (M * x ^ 4) := by omega
      _ = 6 * (2 * (M * x ^ 4)) := by ring
      _ ≤ D * N := hSmallScaled
  have hDistanceScale : 4 * (M * x ^ 4) ≤ D * N := by
    calc
      4 * (M * x ^ 4) ≤ 12 * (M * x ^ 4) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 6 * (2 * (M * x ^ 4)) := by ring
      _ ≤ D * N := hSmallScaled
  have hRectangleScale :
      4 * (S * x ^ 7) ≤ (M * x ^ 4) * (D * N) := by
    calc
      4 * (S * x ^ 7) = (4 * S) * x ^ 7 := by ring
      _ ≤ (M * D * x ^ 3) * x ^ 7 :=
        Nat.mul_le_mul_right _ hRectangle
      _ = (M * x ^ 4) * (D * x ^ 6) := by ring
      _ ≤ (M * x ^ 4) * (D * N) := by gcongr
  exact ⟨hDistancePositive, hLength, hSmallScaled, hRankScaled,
    hFour, hDistanceScale, hRectangleScale⟩
end QEC.Coding.TannerLiftedProduct
