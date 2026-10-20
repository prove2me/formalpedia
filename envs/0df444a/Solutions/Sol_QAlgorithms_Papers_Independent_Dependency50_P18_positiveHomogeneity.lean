-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.positiveHomogeneity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:47:13.47026+00:00
-- url     : https://prove2.me/submissions/45179440-471d-41cd-8da4-80d19d09e46f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

lemma g52a_ereal_sInf_mul (c : ℝ) (hc : 0 < c) (S : Set EReal) :
    sInf ((fun r => (c : EReal) * r) '' S) = (c : EReal) * sInf S := by
  have h1 : ((c : EReal) * ((c⁻¹ : ℝ) : EReal)) = 1 := by
    rw [← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one]
  have h2 : (((c⁻¹ : ℝ) : EReal) * (c : EReal)) = 1 := by
    rw [← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one]
  have hc0 : (0 : EReal) ≤ (c : EReal) := by exact_mod_cast hc.le
  have hc1 : (0 : EReal) ≤ ((c⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_nonneg.mpr hc.le)
  let e : EReal ≃o EReal :=
    { toFun := fun x => (c : EReal) * x
      invFun := fun x => ((c⁻¹ : ℝ) : EReal) * x
      left_inv := fun x => by simp only; rw [← mul_assoc, h2, one_mul]
      right_inv := fun x => by simp only; rw [← mul_assoc, h1, one_mul]
      map_rel_iff' := by
        intro a b
        simp only [Equiv.coe_fn_mk]
        constructor
        · intro h
          have := mul_le_mul_of_nonneg_left h hc1
          rwa [← mul_assoc, ← mul_assoc, h2, one_mul, one_mul] at this
        · intro h; exact mul_le_mul_of_nonneg_left h hc0 }
  have := e.map_sInf S
  rw [sInf_image]
  exact this.symm

lemma g52a_smul_kron {A B : Type} (c : ℂ) (k : Matrix A A ℂ) (l : Matrix B B ℂ) :
    Matrix.kronecker (c • k) l = c • Matrix.kronecker k l := by
  ext i j; simp [Matrix.kronecker, mul_assoc]

lemma g52a_feasible_smul {A B : Type} [Fintype A] [Fintype B]
    (s : Matrix (A × B) (A × B) ℂ) (k : Matrix A A ℂ) (l : Matrix B B ℂ)
    (v : Matrix (A × B) (A × B) ℂ) (c : ℝ) (hc : 0 < c) (h : GammaFeasible s k l v) :
    GammaFeasible ((c : ℂ) • s) ((c : ℂ) • k) l ((c : ℂ) • v) := by
  obtain ⟨hk, hl, hv, h1, h2, h3, h4⟩ := h
  have hc' : (0 : ℂ) ≤ (c : ℂ) := by exact_mod_cast hc.le
  have herm : ∀ {I : Type} (M : Matrix I I ℂ), M.IsHermitian → ((c : ℂ) • M).IsHermitian := by
    intro I M hM
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hM.eq]
    simp
  have hg : ∀ X : Matrix (A × B) (A × B) ℂ,
      QAlgorithms.Papers.Independent.Information100.P04.gamma ((c : ℂ) • X) =
        (c : ℂ) • QAlgorithms.Papers.Independent.Information100.P04.gamma X := by
    intro X; ext i j; rfl
  refine ⟨herm k hk, hl, herm v hv, ?_, ?_, ?_, ?_⟩
  · rw [← smul_add, hg]; exact h1.smul hc'
  · rw [← smul_sub, hg]; exact h2.smul hc'
  · rw [g52a_smul_kron, ← smul_add]; exact h3.smul hc'
  · rw [g52a_smul_kron, ← smul_sub]; exact h4.smul hc'

lemma g52a_trace_smul {A B : Type} [Fintype A] [Fintype B]
    (k : Matrix A A ℂ) (l : Matrix B B ℂ) (c : ℝ) :
    ((Matrix.kronecker ((c : ℂ) • k) l).trace.re : EReal) =
      (c : EReal) * ((Matrix.kronecker k l).trace.re : EReal) := by
  rw [g52a_smul_kron, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    EReal.coe_mul]

/-- Proposition 6, PDF p.3, (16): degree-one homogeneity, allowing sigma=0. -/
theorem solution (sigma : Matrix (A × B) (A × B) ℂ)
    (hsigma : sigma.PosSemidef) (c : ℝ) (hc : 0 < c) :
    correlationGauge ((c : ℂ) • sigma) = (c : EReal) * correlationGauge sigma := by
  unfold correlationGauge
  rw [← g52a_ereal_sInf_mul c hc]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨k, l, v, hf, rfl⟩
    have hci : 0 < c⁻¹ := inv_pos.mpr hc
    have hf' := g52a_feasible_smul _ k l v c⁻¹ hci hf
    have hs : ((c⁻¹ : ℝ) : ℂ) • ((c : ℂ) • sigma) = sigma := by
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_smul]
    rw [hs] at hf'
    refine ⟨_, ⟨_, _, _, hf', rfl⟩, ?_⟩
    rw [g52a_trace_smul, ← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one,
      one_mul]
  · rintro ⟨r', ⟨k, l, v, hf, rfl⟩, rfl⟩
    exact ⟨_, _, _, g52a_feasible_smul _ k l v c hc hf, (g52a_trace_smul k l c).symm⟩


end

