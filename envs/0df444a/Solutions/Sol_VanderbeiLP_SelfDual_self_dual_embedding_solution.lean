-- Prove2me | solution 1 for VanderbeiLP.SelfDual.self_dual_embedding_solution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:43:37.013559+00:00
-- url     : https://prove2.me/submissions/d2588c21-ec2f-41c0-b452-e86c5bebf0d9

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_SelfDualEmbedding

set_option autoImplicit false
open Matrix VanderbeiLP.SelfDual

theorem dot_AT {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    x ⬝ᵥ (Aᵀ *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

theorem dot_nn {k : ℕ} (u v : Fin k → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ u ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_nonneg (hu i) (hv i)

theorem dot_mono {k : ℕ} (u v w : Fin k → ℝ) (hu : ∀ i, 0 ≤ u i) (hvw : ∀ i, v i ≤ w i) :
    u ⬝ᵥ v ≤ u ⬝ᵥ w :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hvw i) (hu i)

theorem weak_dual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j) (hy : ∀ i, 0 ≤ y i)
    (hP : ∀ i, (A *ᵥ x) i ≤ b i) (hD : ∀ j, c j ≤ (Aᵀ *ᵥ y) j) : c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  have h1 : x ⬝ᵥ c ≤ x ⬝ᵥ (Aᵀ *ᵥ y) := dot_mono x c _ hx hD
  have h2 : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ b := dot_mono y _ b hy hP
  rw [dot_AT] at h1
  rw [dotProduct_comm c x, dotProduct_comm b y]
  linarith

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (φ : ℝ) (z : Fin n → ℝ) (w : Fin m → ℝ) (ψ : ℝ)
    (hfeas : EmbeddingFeasible A b c x y φ z w ψ)
    (hsc : EmbeddingStrictlyComplementary x y φ z w ψ) :
    (0 < φ → VanderbeiLP.StrictComp.PrimalOptimal A b c (φ⁻¹ • x) ∧ VanderbeiLP.StrictComp.DualOptimal A b c (φ⁻¹ • y)) ∧
    (φ = 0 →
      (0 < c ⬝ᵥ x ∨ b ⬝ᵥ y < 0) ∧
      (0 < c ⬝ᵥ x → ¬ ∃ y' : Fin m → ℝ, DualFeasible A c y') ∧
      (b ⬝ᵥ y < 0 → ¬ ∃ x' : Fin n → ℝ, PrimalFeasible A b x')) := by
  obtain ⟨h1, h2, h3, hx, hy, hφ, hz, hw, hψ⟩ := hfeas
  obtain ⟨-, -, hφψ⟩ := hsc
  have hzE : ∀ j, z j = (Aᵀ *ᵥ y) j - φ * c j := by
    intro j
    have := congrFun h1 j
    simp at this
    linarith
  have hwE : ∀ i, w i = φ * b i - (A *ᵥ x) i := by
    intro i
    have := congrFun h2 i
    simp at this
    linarith
  have hψE : ψ = c ⬝ᵥ x - b ⬝ᵥ y := by linarith
  refine ⟨?_, ?_⟩
  · intro hφp
    -- complementarity φ ψ = 0
    have hzv : z = Aᵀ *ᵥ y - φ • c := by ext j; simp [hzE j]
    have hwv : w = φ • b - A *ᵥ x := by ext i; simp [hwE i]
    have hS : x ⬝ᵥ z + y ⬝ᵥ w + φ * ψ = 0 := by
      rw [hzv, hwv, hψE, dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul,
        dot_AT, dotProduct_comm x c, dotProduct_comm y b]
      simp only [smul_eq_mul]
      ring
    have n1 : 0 ≤ x ⬝ᵥ z := dot_nn x z hx hz
    have n2 : 0 ≤ y ⬝ᵥ w := dot_nn y w hy hw
    have n3 : 0 ≤ φ * ψ := mul_nonneg hφ hψ
    have hψ0 : ψ = 0 := by
      have : φ * ψ = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hφp.ne'
      · exact h
    have hcb : c ⬝ᵥ x = b ⬝ᵥ y := by linarith
    have hxs : ∀ j, 0 ≤ (φ⁻¹ • x) j := fun j => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hφ) (hx j)
    have hys : ∀ i, 0 ≤ (φ⁻¹ • y) i := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.mpr hφ) (hy i)
    have hP : ∀ i, (A *ᵥ (φ⁻¹ • x)) i ≤ b i := by
      intro i
      rw [Matrix.mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      have := hw i
      rw [hwE i] at this
      have h' : (A *ᵥ x) i ≤ φ * b i := by linarith
      calc φ⁻¹ * (A *ᵥ x) i ≤ φ⁻¹ * (φ * b i) :=
            mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hφ)
        _ = b i := by field_simp
    have hD : ∀ j, c j ≤ (Aᵀ *ᵥ (φ⁻¹ • y)) j := by
      intro j
      rw [Matrix.mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      have := hz j
      rw [hzE j] at this
      have h' : φ * c j ≤ (Aᵀ *ᵥ y) j := by linarith
      calc c j = φ⁻¹ * (φ * c j) := by field_simp
        _ ≤ φ⁻¹ * (Aᵀ *ᵥ y) j := mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hφ)
    have hobj : c ⬝ᵥ (φ⁻¹ • x) = b ⬝ᵥ (φ⁻¹ • y) := by
      rw [dotProduct_smul, dotProduct_smul, hcb]
    refine ⟨⟨⟨hxs, fun i => ?_⟩, fun x' hx' => ?_⟩, ⟨⟨hys, fun j => ?_⟩, fun y' hy' => ?_⟩⟩
    · unfold VanderbeiLP.StrictComp.primalSlack
      simp only [Pi.sub_apply]
      linarith [hP i]
    · have := weak_dual A b c x' (φ⁻¹ • y) hx'.1 hys
        (fun i => by have := hx'.2 i; unfold VanderbeiLP.StrictComp.primalSlack at this
                     simp only [Pi.sub_apply] at this; linarith) hD
      linarith
    · unfold VanderbeiLP.StrictComp.dualSlack
      simp only [Pi.sub_apply]
      linarith [hD j]
    · have := weak_dual A b c (φ⁻¹ • x) y' hxs hy'.1 hP
        (fun j => by have := hy'.2 j; unfold VanderbeiLP.StrictComp.dualSlack at this
                     simp only [Pi.sub_apply] at this; linarith)
      linarith
  · intro hφ0
    subst hφ0
    have hpos : 0 < ψ := by linarith
    have hlt : b ⬝ᵥ y < c ⬝ᵥ x := by linarith
    refine ⟨?_, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      linarith [hcon.1, hcon.2]
    · intro hc ⟨y', hy'0, hy'⟩
      have hAx : ∀ i, (A *ᵥ x) i ≤ 0 := by
        intro i; have := hwE i; have := hw i; simp at *; linarith
      have e1 : x ⬝ᵥ c ≤ x ⬝ᵥ (Aᵀ *ᵥ y') := dot_mono x c _ hx hy'
      have e2 : y' ⬝ᵥ (A *ᵥ x) ≤ y' ⬝ᵥ 0 := dot_mono y' _ 0 hy'0 hAx
      rw [dot_AT] at e1
      rw [dotProduct_comm x c] at e1
      simp at e2
      linarith
    · intro hb ⟨x', hx'0, hx'⟩
      have hAy : ∀ j, 0 ≤ (Aᵀ *ᵥ y) j := by
        intro j; have := hzE j; have := hz j; simp at *; linarith
      have e1 : 0 ≤ x' ⬝ᵥ (Aᵀ *ᵥ y) := dot_nn x' _ hx'0 hAy
      have e2 : y ⬝ᵥ (A *ᵥ x') ≤ y ⬝ᵥ b := dot_mono y _ b hy hx'
      rw [dot_AT] at e1
      rw [dotProduct_comm b y] at hb
      linarith
