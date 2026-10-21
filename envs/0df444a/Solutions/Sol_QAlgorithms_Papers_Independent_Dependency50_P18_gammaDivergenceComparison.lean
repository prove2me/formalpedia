-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.gammaDivergenceComparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T06:01:50.507448+00:00
-- url     : https://prove2.me/submissions/d1746142-f7e2-42f5-8505-917b7bdda75e

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

lemma h54d_ereal_sInf_mul (c : ℝ) (hc : 0 < c) (S : Set EReal) :
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

lemma h54d_smul_kron {A B : Type} (c : ℂ) (k : Matrix A A ℂ) (l : Matrix B B ℂ) :
    Matrix.kronecker (c • k) l = c • Matrix.kronecker k l := by
  ext i j; simp [Matrix.kronecker, mul_assoc]

lemma h54d_feasible_smul {A B : Type} [Fintype A] [Fintype B]
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
  · rw [h54d_smul_kron, ← smul_add]; exact h3.smul hc'
  · rw [h54d_smul_kron, ← smul_sub]; exact h4.smul hc'

lemma h54d_trace_smul {A B : Type} [Fintype A] [Fintype B]
    (k : Matrix A A ℂ) (l : Matrix B B ℂ) (c : ℝ) :
    ((Matrix.kronecker ((c : ℂ) • k) l).trace.re : EReal) =
      (c : EReal) * ((Matrix.kronecker k l).trace.re : EReal) := by
  rw [h54d_smul_kron, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    EReal.coe_mul]

lemma h54d_homog (sigma : Matrix (A × B) (A × B) ℂ) (c : ℝ) (hc : 0 < c) :
    correlationGauge ((c : ℂ) • sigma) = (c : EReal) * correlationGauge sigma := by
  unfold correlationGauge
  rw [← h54d_ereal_sInf_mul c hc]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨k, l, v, hf, rfl⟩
    have hci : 0 < c⁻¹ := inv_pos.mpr hc
    have hf' := h54d_feasible_smul _ k l v c⁻¹ hci hf
    have hs : ((c⁻¹ : ℝ) : ℂ) • ((c : ℂ) • sigma) = sigma := by
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_smul]
    rw [hs] at hf'
    refine ⟨_, ⟨_, _, _, hf', rfl⟩, ?_⟩
    rw [h54d_trace_smul, ← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne', EReal.coe_one,
      one_mul]
  · rintro ⟨r', ⟨k, l, v, hf, rfl⟩, rfl⟩
    exact ⟨_, _, _, h54d_feasible_smul _ k l v c hc hf, (h54d_trace_smul k l c).symm⟩

open scoped MatrixOrder Matrix.Norms.L2Operator in
lemma h54d_herm_bound {I : Type*} [Fintype I] [DecidableEq I] (H : Matrix I I ℂ)
    (hH : H.IsHermitian) : ∃ c : ℝ, 0 ≤ c ∧ ((c : ℂ) • (1 : Matrix I I ℂ) - H).PosSemidef ∧
      ((c : ℂ) • (1 : Matrix I I ℂ) + H).PosSemidef := by
  have h1 := IsSelfAdjoint.le_algebraMap_norm_self (a := H) hH
  have h2 := IsSelfAdjoint.neg_algebraMap_norm_le_self (a := H) hH
  rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h1 h2
  refine ⟨‖H‖, norm_nonneg _, ?_, ?_⟩
  · rw [Complex.coe_smul]; exact h1
  · rw [Complex.coe_smul]; simpa [sub_neg_eq_add, add_comm] using h2

lemma h54d_gamma_trace {A B : Type} [Fintype A] [Fintype B] (X : Matrix (A × B) (A × B) ℂ) :
    (QAlgorithms.Papers.Independent.Information100.P04.gamma X).trace = X.trace := by
  simp [Matrix.trace, QAlgorithms.Papers.Independent.Information100.P04.gamma]

lemma h54d_re_nonneg {I : Type} [Fintype I] {M : Matrix I I ℂ} (h : M.PosSemidef) :
    0 ≤ M.trace.re := (Complex.le_def.mp h.trace_nonneg).1

lemma h54d_trace_le {A B : Type} [Fintype A] [Fintype B]
    (s : Matrix (A × B) (A × B) ℂ) (k : Matrix A A ℂ) (l : Matrix B B ℂ)
    (v : Matrix (A × B) (A × B) ℂ) (h : GammaFeasible s k l v) :
    s.trace.re ≤ (Matrix.kronecker k l).trace.re := by
  obtain ⟨_, _, _, _, h2, _, h4⟩ := h
  have a := h54d_re_nonneg h2
  have b := h54d_re_nonneg h4
  rw [h54d_gamma_trace, Matrix.trace_sub, Complex.sub_re] at a
  rw [Matrix.trace_sub, Complex.sub_re] at b
  linarith

lemma h54d_gauge_ge (s : Matrix (A × B) (A × B) ℂ) :
    (s.trace.re : EReal) ≤ correlationGauge s := by
  unfold correlationGauge
  apply le_sInf
  rintro r ⟨k, l, v, hf, rfl⟩
  exact_mod_cast h54d_trace_le s k l v hf

lemma h54d_gamma_one :
    QAlgorithms.Papers.Independent.Information100.P04.gamma (1 : Matrix (A × B) (A × B) ℂ) = 1 := by
  ext i j
  simp only [QAlgorithms.Papers.Independent.Information100.P04.gamma, Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2 <;> simp [h1, h2, eq_comm]

lemma h54d_gauge_lt (s : Matrix (A × B) (A × B) ℂ) (hs : s.IsHermitian) :
    correlationGauge s < ⊤ := by
  have hG : (QAlgorithms.Papers.Independent.Information100.P04.gamma s).IsHermitian := by
    ext i j
    have := congrFun (congrFun hs (i.1, j.2)) (j.1, i.2)
    simpa [QAlgorithms.Papers.Independent.Information100.P04.gamma, Matrix.conjTranspose_apply] using this
  obtain ⟨c, hc, h1, h2⟩ := h54d_herm_bound _ hG
  have hk : Matrix.kronecker ((c : ℂ) • (1 : Matrix A A ℂ)) (1 : Matrix B B ℂ) = (c : ℂ) • 1 := by
    rw [h54d_smul_kron]; congr 1; exact Matrix.one_kronecker_one
  have hf : GammaFeasible s ((c : ℂ) • 1) 1 ((c : ℂ) • 1) := by
    have hc' : (0 : ℂ) ≤ (c : ℂ) := by exact_mod_cast hc
    have hg : ∀ X Y : Matrix (A × B) (A × B) ℂ, ∀ z : ℂ,
        QAlgorithms.Papers.Independent.Information100.P04.gamma (z • X + Y) =
        z • QAlgorithms.Papers.Independent.Information100.P04.gamma X +
          QAlgorithms.Papers.Independent.Information100.P04.gamma Y := by
      intro X Y z; ext i j; rfl
    refine ⟨?_, Matrix.isHermitian_one, ?_, ?_, ?_, ?_, ?_⟩
    · unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_smul]; simp
    · unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_smul]; simp
    · rw [← add_zero ((c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ)), add_assoc, zero_add, hg,
        h54d_gamma_one]; exact h2
    · rw [sub_eq_add_neg, hg, h54d_gamma_one]
      have : QAlgorithms.Papers.Independent.Information100.P04.gamma (-s) =
        -QAlgorithms.Papers.Independent.Information100.P04.gamma s := by ext i j; rfl
      rw [this, ← sub_eq_add_neg]; exact h1
    · rw [hk, ← add_smul]
      exact Matrix.PosSemidef.one.smul (by
        have : (0:ℂ) ≤ (c:ℂ) + c := by exact_mod_cast (by linarith : (0:ℝ) ≤ c + c)
        exact this)
    · rw [hk, sub_self]; exact Matrix.PosSemidef.zero
  have : correlationGauge s ≤
      ((Matrix.kronecker ((c : ℂ) • (1 : Matrix A A ℂ)) (1 : Matrix B B ℂ)).trace.re : EReal) :=
    sInf_le ⟨_, _, _, hf, rfl⟩
  exact lt_of_le_of_lt this (EReal.coe_lt_top _)

lemma h54d_gauge_real (rho : Matrix (A × B) (A × B) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    ∃ g : ℝ, 1 ≤ g ∧ correlationGauge rho = (g : EReal) := by
  have h1 := h54d_gauge_ge rho
  rw [hrho.2] at h1
  simp only [Complex.one_re, EReal.coe_one] at h1
  have h2 := h54d_gauge_lt rho hrho.1.1
  have h1b : (1:EReal) ≠ ⊥ := by simpa using EReal.coe_ne_bot 1
  have hb : correlationGauge rho ≠ ⊥ := by
    intro h; rw [h, le_bot_iff] at h1; exact h1b h1
  refine ⟨(correlationGauge rho).toReal, ?_, (EReal.coe_toReal h2.ne hb).symm⟩
  have := EReal.toReal_le_toReal h1 h1b h2.ne
  simpa using this

theorem solution (D : Divergence) (hD : IsGeneralizedDivergence D)
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    capitalGamma D rho ≤ D rho (normalizedComparison rho) ∧
      D rho (normalizedComparison rho) = cGamma rho := by
  obtain ⟨g, hg1, hg⟩ := h54d_gauge_real rho hrho
  have hg0 : 0 < g := by linarith
  have hN : normalizedComparison rho = ((g⁻¹ : ℝ) : ℂ) • rho := by
    unfold normalizedComparison; rw [hg, EReal.toReal_coe, Complex.ofReal_inv]
  have hD' : D rho (normalizedComparison rho) = (Real.logb 2 g : EReal) := by
    rw [hN, hD.scaling rho rho _ hrho hrho.1 (inv_pos.mpr hg0), hD.zeroValue rho hrho,
      Real.logb_inv, ← EReal.coe_zero, ← EReal.coe_sub]
    congr 1; ring
  refine ⟨?_, ?_⟩
  · apply sInf_le
    refine ⟨normalizedComparison rho, ?_, ?_, rfl⟩
    · rw [hN]; exact hrho.1.smul (by exact_mod_cast (inv_pos.mpr hg0).le)
    · rw [hN, h54d_homog rho _ (inv_pos.mpr hg0), hg, ← EReal.coe_mul, inv_mul_cancel₀ hg0.ne']
      simp
  · rw [hD']
    unfold cGamma logBits
    rw [hg]
    have : (g : EReal) ≠ 0 := by exact_mod_cast hg0.ne'
    simp [this]

end
