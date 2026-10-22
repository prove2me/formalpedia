-- Prove2me | solution 1 for TinyCoreset.DimRed.claim3_pythagoras
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:23:14.640353+00:00
-- url     : https://prove2.me/submissions/67001a7c-8eca-480d-9e4b-4aabc68042ab

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting
set_option autoImplicit false
open scoped Matrix
open TinyCoreset.DimRed

lemma tcd_frob_eq_trace {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    frobSq M = (M * Mᵀ).trace := by
  simp [frobSq, Matrix.trace, Matrix.mul_apply, sq]

lemma tcd_proj_sum {d j : ℕ} (hjd : j ≤ d)
    (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ)
    (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (hXY : Xᵀ * Y = 0) :
    X * Xᵀ + Y * Yᵀ = 1 := by
  have hYX : Yᵀ * X = 0 := by
    have := congrArg Matrix.transpose hXY
    simpa [Matrix.transpose_mul] using this
  have e : Fin d ≃ Fin j ⊕ Fin (d - j) :=
    (finCongr (by omega : d = j + (d - j))).trans finSumFinEquiv.symm
  have hM : Matrix.fromRows Xᵀ Yᵀ * Matrix.fromCols X Y = 1 := by
    rw [Matrix.fromRows_mul_fromCols, hX, hY, hXY, hYX, Matrix.fromBlocks_one]
  have h2 := (Matrix.fromCols_mul_fromRows_eq_one_comm e X Y Xᵀ Yᵀ).2 hM
  rwa [Matrix.fromCols_mul_fromRows] at h2

theorem solution {n d j : ℕ} (hjd : j ≤ d)
    (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ)
    (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (hXY : Xᵀ * Y = 0)
    (A : Matrix (Fin n) (Fin d) ℝ) :
    frobSq A = frobSq (A * X) + frobSq (A * Y) := by
  have h := tcd_proj_sum hjd X Y hX hY hXY
  rw [tcd_frob_eq_trace, tcd_frob_eq_trace, tcd_frob_eq_trace, ← Matrix.trace_add]
  have : A * Xᵀ.transpose = A * X := by simp
  have e1 : A * X * (A * X)ᵀ = A * (X * Xᵀ) * Aᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have e2 : A * Y * (A * Y)ᵀ = A * (Y * Yᵀ) * Aᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, h]
  simp
