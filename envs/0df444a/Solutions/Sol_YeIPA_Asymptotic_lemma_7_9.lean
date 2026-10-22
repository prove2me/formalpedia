-- Prove2me | solution 1 for YeIPA.Asymptotic.lemma_7_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:47:02.129803+00:00
-- url     : https://prove2.me/submissions/cb8f47e7-2f5c-4242-a8da-4a93b3cc5545

import Mathlib

open Matrix

theorem g69c_quad {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hM : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v)) (v0 : ι → ℝ) (h0 : v0 ⬝ᵥ (M *ᵥ v0) = 0)
    (w : ι → ℝ) : w ⬝ᵥ (M *ᵥ v0) + v0 ⬝ᵥ (M *ᵥ w) = 0 := by
  set a := w ⬝ᵥ (M *ᵥ v0) + v0 ⬝ᵥ (M *ᵥ w)
  set b := w ⬝ᵥ (M *ᵥ w)
  have hb : 0 ≤ b := hM w
  have key : ∀ t : ℝ, 0 ≤ t * a + t ^ 2 * b := by
    intro t
    have h := hM (v0 + t • w)
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, h0] at h
    have : t * a + t ^ 2 * b = 0 + t * (v0 ⬝ᵥ (M *ᵥ w)) + (t * (w ⬝ᵥ (M *ᵥ v0)) +
        t * (t * (w ⬝ᵥ (M *ᵥ w)))) := by simp only [a, b]; ring
    linarith
  have h1 := key (-a / (b + 1))
  have hb1 : 0 < b + 1 := by linarith
  have e : -a / (b + 1) * a + (-a / (b + 1)) ^ 2 * b = -(a ^ 2 / (b + 1) ^ 2) := by
    field_simp; ring
  rw [e] at h1
  have : a ^ 2 / (b + 1) ^ 2 ≤ 0 := by linarith
  have h2 : a ^ 2 ≤ 0 := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < (b + 1) ^ 2)).mp this
    linarith
  nlinarith [sq_nonneg a]

theorem g69c_vec_zero {ι : Type*} [Fintype ι] (u : ι → ℝ) (h : ∀ w : ι → ℝ, w ⬝ᵥ u = 0) :
    u = 0 := dotProduct_self_eq_zero.mp (h u)

theorem g69c_block_facts {p z : Type*} [Fintype p] [Fintype z] [DecidableEq p] [DecidableEq z]
    (MPP : Matrix p p ℝ) (MPZ : Matrix p z ℝ) (MZP : Matrix z p ℝ) (MZZ : Matrix z z ℝ)
    (hM : ∀ v : p ⊕ z → ℝ, 0 ≤ v ⬝ᵥ (Matrix.fromBlocks MPP MPZ MZP MZZ *ᵥ v))
    (xP : p → ℝ) (h0 : xP ⬝ᵥ (MPP *ᵥ xP) = 0) :
    MPP *ᵥ xP + MPPᵀ *ᵥ xP = 0 ∧ (MZP + MPZᵀ) *ᵥ xP = 0 := by
  set M := Matrix.fromBlocks MPP MPZ MZP MZZ
  set v0 : p ⊕ z → ℝ := Sum.elim xP 0
  have hMv0 : M *ᵥ v0 = Sum.elim (MPP *ᵥ xP) (MZP *ᵥ xP) := by
    simp [M, v0, fromBlocks_mulVec]
  have hq : v0 ⬝ᵥ (M *ᵥ v0) = 0 := by
    rw [hMv0]; simp [v0, sumElim_dotProduct_sumElim, h0]
  constructor
  · apply g69c_vec_zero
    intro wP
    have := g69c_quad M hM v0 hq (Sum.elim wP 0)
    have hMw : M *ᵥ Sum.elim wP 0 = Sum.elim (MPP *ᵥ wP) (MZP *ᵥ wP) := by
      simp [M, fromBlocks_mulVec]
    rw [hMv0, hMw] at this
    simp only [v0, sumElim_dotProduct_sumElim, zero_dotProduct, add_zero] at this
    rw [dotProduct_add, mulVec_transpose, dotProduct_comm wP (xP ᵥ* MPP), ← dotProduct_mulVec]
    exact this
  · apply g69c_vec_zero
    intro wZ
    have := g69c_quad M hM v0 hq (Sum.elim 0 wZ)
    have hMw : M *ᵥ Sum.elim 0 wZ = Sum.elim (MPZ *ᵥ wZ) (MZZ *ᵥ wZ) := by
      simp [M, fromBlocks_mulVec]
    rw [hMv0, hMw] at this
    simp only [v0, sumElim_dotProduct_sumElim, zero_dotProduct, dotProduct_zero, zero_add,
      add_zero] at this
    rw [add_mulVec, dotProduct_add, mulVec_transpose, dotProduct_comm wZ (xP ᵥ* MPZ),
      ← dotProduct_mulVec]
    exact this

theorem solution {p z : Type*} [Fintype p] [Fintype z] [DecidableEq p] [DecidableEq z]
    (MPP : Matrix p p ℝ) (MPZ : Matrix p z ℝ) (MZP : Matrix z p ℝ) (MZZ : Matrix z z ℝ)
    (hM : ∀ v : p ⊕ z → ℝ, 0 ≤ v ⬝ᵥ (Matrix.fromBlocks MPP MPZ MZP MZZ *ᵥ v))
    (xP : p → ℝ) :
    (MPP *ᵥ xP = 0 ↔ MPPᵀ *ᵥ xP = 0) ∧
      (MPP *ᵥ xP = 0 → (MZP + MPZᵀ) *ᵥ xP = 0) := by
  have hT : xP ⬝ᵥ (MPP *ᵥ xP) = (MPPᵀ *ᵥ xP) ⬝ᵥ xP := by
    rw [mulVec_transpose, dotProduct_mulVec]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · have h0 : xP ⬝ᵥ (MPP *ᵥ xP) = 0 := by rw [h, dotProduct_zero]
    have := (g69c_block_facts MPP MPZ MZP MZZ hM xP h0).1
    rw [h, zero_add] at this; exact this
  · have h0 : xP ⬝ᵥ (MPP *ᵥ xP) = 0 := by rw [hT, h, zero_dotProduct]
    have := (g69c_block_facts MPP MPZ MZP MZZ hM xP h0).1
    rw [h, add_zero] at this; exact this
  · have h0 : xP ⬝ᵥ (MPP *ᵥ xP) = 0 := by rw [h, dotProduct_zero]
    exact (g69c_block_facts MPP MPZ MZP MZZ hM xP h0).2
