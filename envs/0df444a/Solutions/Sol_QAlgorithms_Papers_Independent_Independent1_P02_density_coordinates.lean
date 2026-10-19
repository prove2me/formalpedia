-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.density_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:02:33.685912+00:00
-- url     : https://prove2.me/submissions/593ef6e3-8d41-483e-a925-081eff4bac17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P02
/-- Eq.(23), PDF p.12. Proposed correction w_0=d^(-1/2) replaces printed
d^(1/2), forced by trace one and G_0=I/sqrt(d). Pending independent moderation. -/
theorem gk_herm_im {d : ℕ} (A B : Algebra d) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace.im = 0 := by
  have h : star ((A * B).trace) = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  have := congrArg Complex.im h
  simp at this
  linarith

theorem gk_frame_zero {d : ℕ} (G : HermitianFrame d) (H : Algebra d) (hH : H.IsHermitian)
    (h : ∀ j, (H * G.matrix j).trace.re = 0) : H = 0 := by
  have hs := G.spans H hH
  have key : ∀ Y ∈ Submodule.span ℝ (Set.range G.matrix), (H * Y).trace.re = 0 := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, hx, smul_zero]
  have h1 := key H hs
  have h2 := gk_herm_im H H hH hH
  have h3 : (Hᴴ * H).trace = 0 := by
    rw [hH.eq]; exact Complex.ext h1 h2
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h3

theorem gk_purity_le {d : ℕ} (rho : Algebra d) (hrho : IsDensityMatrix rho) :
    (rho * rho).trace.re ≤ 1 := by
  have hA := hrho.1.isHermitian
  set X := Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) with hX
  have hs : rho = X := hA.spectral_theorem
  have e1 : rho * rho = X * X := by rw [← hs]
  have e2 : (rho * rho).trace = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ)^2 := by
    rw [e1, hX, ← map_mul, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.diagonal_mul_diagonal,
      Matrix.trace_diagonal]
    simp [pow_two]
  have e3 : ∑ i, hA.eigenvalues i = 1 := by
    have := hA.trace_eq_sum_eigenvalues
    rw [hrho.2] at this
    have := congrArg Complex.re this
    simpa using this.symm
  have hnn : ∀ i, 0 ≤ hA.eigenvalues i := fun i => hrho.1.eigenvalues_nonneg i
  rw [e2]
  have : (∑ i, ((hA.eigenvalues i : ℝ) : ℂ)^2).re = ∑ i, (hA.eigenvalues i)^2 := by
    rw [Complex.re_sum]; congr 1; ext i; rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [this, ← e3]
  apply Finset.sum_le_sum
  intro i _
  have : hA.eigenvalues i ≤ 1 := by
    rw [← e3]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  nlinarith [hnn i]

theorem solution (d : ℕ) (G : HermitianFrame d) (rho : Algebra d)
    (hDensity : IsDensityMatrix rho) :
    (∀ j, (rho*G.matrix j).trace = (hermitianCoordinates G rho j : ℂ)) ∧
    rho = ∑ j, (hermitianCoordinates G rho j : ℂ) • G.matrix j ∧
    rho = ((d : ℂ)⁻¹) • 1 + ∑ j ∈ Finset.univ.filter (fun j : Fin (d^2) => j.val ≠ 0),
      (hermitianCoordinates G rho j : ℂ) • G.matrix j ∧
    hermitianCoordinates G rho ⟨0,by have := G.positive; positivity⟩ = (Real.sqrt d)⁻¹ ∧
    (∑ j, (hermitianCoordinates G rho j)^2) = (rho*rho).trace.re ∧
    (rho*rho).trace.re ≤ 1 ∧
    (∑ j ∈ Finset.univ.filter (fun j : Fin (d^2) => j.val ≠ 0),
      (hermitianCoordinates G rho j)^2) ≤ ((d : ℝ)-1)/d := by
  have hd := G.positive
  have hH := hDensity.1.isHermitian
  set c := hermitianCoordinates G rho with hc
  set z : Fin (d^2) := ⟨0, by positivity⟩ with hz
  have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have h1 : ∀ j, (rho*G.matrix j).trace = (c j : ℂ) := by
    intro j
    exact Complex.ext (by simp [hc, hermitianCoordinates])
      (by simp [gk_herm_im _ _ hH (G.hermitian j)])
  have h2 : rho = ∑ j, (c j : ℂ) • G.matrix j := by
    have hsumH : (∑ j, (c j : ℂ) • G.matrix j).IsHermitian := by
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_sum]
      congr 1; ext1 j
      rw [Matrix.conjTranspose_smul, (G.hermitian j).eq]
      simp
    have := gk_frame_zero G (rho - ∑ j, (c j : ℂ) • G.matrix j) (hH.sub hsumH) (fun n => ?_)
    · exact sub_eq_zero.1 this
    · rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Finset.sum_mul, Matrix.trace_sum,
        Complex.re_sum]
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
        G.orthonormal]
      simp [hc, hermitianCoordinates]
  have h4 : c z = (Real.sqrt d)⁻¹ := by
    simp only [hc, hermitianCoordinates, hz, G.identity, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, hDensity.2, smul_eq_mul, mul_one]
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
  have hsplit : ∀ f : Fin (d^2) → ℝ, ∑ j, f j =
      f z + ∑ j ∈ Finset.univ.filter (fun j : Fin (d^2) => j.val ≠ 0), f j := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin (d^2) => j.val ≠ 0) f]
    have : Finset.univ.filter (fun j : Fin (d^2) => ¬ j.val ≠ 0) = {z} := by
      ext j; simp [hz, Fin.ext_iff]
    rw [this, Finset.sum_singleton, add_comm]
  have hsplitC : ∀ f : Fin (d^2) → Algebra d, ∑ j, f j =
      f z + ∑ j ∈ Finset.univ.filter (fun j : Fin (d^2) => j.val ≠ 0), f j := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin (d^2) => j.val ≠ 0) f]
    have : Finset.univ.filter (fun j : Fin (d^2) => ¬ j.val ≠ 0) = {z} := by
      ext j; simp [hz, Fin.ext_iff]
    rw [this, Finset.sum_singleton, add_comm]
  have h5 : (∑ j, (c j)^2) = (rho*rho).trace.re := by
    nth_rewrite 2 [h2]
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    congr 1; ext j
    rw [Matrix.mul_smul, Matrix.trace_smul, h1 j, smul_eq_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re, pow_two]
  have h6 := gk_purity_le rho hDensity
  refine ⟨h1, h2, ?_, h4, h5, h6, ?_⟩
  · conv_lhs => rw [h2]
    rw [hsplitC, h4, G.identity, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 2
    rw [← mul_inv, Real.mul_self_sqrt (by positivity), Complex.ofReal_inv,
      Complex.ofReal_natCast]
  · have := hsplit (fun j => (c j)^2)
    rw [h4, inv_pow, Real.sq_sqrt (by positivity)] at this
    have hdpos : (0:ℝ) < d := by exact_mod_cast hd
    rw [sub_div, div_self hdpos.ne', le_sub_iff_add_le]
    rw [one_div]; linarith

