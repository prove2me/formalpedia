-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rootSchedule_graphThresholds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:33:23.621425+00:00
-- url     : https://prove2.me/submissions/700ca680-8081-47af-b34b-8f0138c667ab

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_log_mul_self_pow_le_add

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
    (A D M S C N x : Nat) (lambda : ℝ) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hLambdaNonnegative : 0 ≤ lambda)
    (hLambda : lambda ≤ ((C * x ^ 3 : Nat) : ℝ))
    (hVertical : 2 * M + C ≤ D * x ^ 2)
    (hEdge : 4 * C ≤ M * x)
    (hFace : 16 * (128 * A + 6 * x + 1) * C ^ 2 ≤ S * x) :
    ((2 * (M * x ^ 4) : Nat) : ℝ) + lambda ≤ (D * N : Nat) ∧
    2 * (2 * lambda) ≤ ((M * x ^ 4 : Nat) : ℝ) ∧
    2 * (((Nat.log 2 (2 * (A * N)) + 1 : Nat) : ℝ) *
      (8 * lambda ^ 2)) ≤ ((S * x ^ 7 : Nat) : ℝ) := by
  have hX3X4 : x ^ 3 ≤ x ^ 4 :=
    Nat.pow_le_pow_right hx (by norm_num)
  have hVerticalNat :
      2 * (M * x ^ 4) + C * x ^ 3 ≤ D * N := by
    calc
      2 * (M * x ^ 4) + C * x ^ 3 ≤
          2 * (M * x ^ 4) + C * x ^ 4 := by
        gcongr
      _ = (2 * M + C) * x ^ 4 := by ring
      _ ≤ (D * x ^ 2) * x ^ 4 := Nat.mul_le_mul_right _ hVertical
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hLower
  have hVerticalReal :
      ((2 * (M * x ^ 4) : Nat) : ℝ) + ((C * x ^ 3 : Nat) : ℝ) ≤
        (D * N : Nat) := by
    exact_mod_cast hVerticalNat
  have hEdgeNat : 4 * (C * x ^ 3) ≤ M * x ^ 4 := by
    calc
      4 * (C * x ^ 3) = (4 * C) * x ^ 3 := by ring
      _ ≤ (M * x) * x ^ 3 := Nat.mul_le_mul_right _ hEdge
      _ = M * x ^ 4 := by ring
  have hEdgeReal :
      4 * ((C * x ^ 3 : Nat) : ℝ) ≤ (M * x ^ 4 : Nat) := by
    exact_mod_cast hEdgeNat
  have hLogArgument : 2 * (A * N) ≤ (128 * A) * x ^ 6 := by
    calc
      2 * (A * N) ≤ 2 * (A * (64 * x ^ 6)) := by gcongr
      _ = (128 * A) * x ^ 6 := by ring
  have hLog : Nat.log 2 (2 * (A * N)) + 1 ≤
      128 * A + 6 * x + 1 := by
    have hBase : Nat.log 2 ((128 * A) * x ^ 6) ≤
        128 * A + x * 6 :=
      log_mul_self_pow_le_add 2 (128 * A) x 6 (by norm_num)
    have hMono : Nat.log 2 (2 * (A * N)) ≤
        Nat.log 2 ((128 * A) * x ^ 6) :=
      Nat.log_mono_right hLogArgument
    omega
  have hLambdaSquare : lambda ^ 2 ≤
      (((C * x ^ 3 : Nat) : ℝ) ^ 2) := by
    exact (sq_le_sq₀ hLambdaNonnegative (by positivity)).2 hLambda
  have hFaceNat :
      16 * (128 * A + 6 * x + 1) * C ^ 2 * x ^ 6 ≤ S * x ^ 7 := by
    calc
      16 * (128 * A + 6 * x + 1) * C ^ 2 * x ^ 6 ≤
          (S * x) * x ^ 6 := Nat.mul_le_mul_right _ hFace
      _ = S * x ^ 7 := by ring
  have hFaceReal :
      16 * ((128 * A + 6 * x + 1 : Nat) : ℝ) *
          (((C * x ^ 3 : Nat) : ℝ) ^ 2) ≤
        ((S * x ^ 7 : Nat) : ℝ) := by
    have hFaceNat' :
        16 * (128 * A + 6 * x + 1) * (C * x ^ 3) ^ 2 ≤ S * x ^ 7 := by
      calc
        16 * (128 * A + 6 * x + 1) * (C * x ^ 3) ^ 2 =
            16 * (128 * A + 6 * x + 1) * C ^ 2 * x ^ 6 := by ring
        _ ≤ S * x ^ 7 := hFaceNat
    exact_mod_cast hFaceNat'
  constructor
  · linarith
  constructor
  · linarith
  · calc
      2 * (((Nat.log 2 (2 * (A * N)) + 1 : Nat) : ℝ) *
          (8 * lambda ^ 2)) =
          16 * ((Nat.log 2 (2 * (A * N)) + 1 : Nat) : ℝ) *
            lambda ^ 2 := by ring
      _ ≤ 16 * ((128 * A + 6 * x + 1 : Nat) : ℝ) *
          (((C * x ^ 3 : Nat) : ℝ) ^ 2) := by
        gcongr
      _ ≤ ((S * x ^ 7 : Nat) : ℝ) := hFaceReal
end QEC.Coding.TannerLiftedProduct
