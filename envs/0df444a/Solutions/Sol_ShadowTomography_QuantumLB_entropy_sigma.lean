-- Prove2me | solution 1 for ShadowTomography.QuantumLB.entropy_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:22:49.941144+00:00
-- url     : https://prove2.me/submissions/fd9968ff-8604-4954-91d3-9802675f5242

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
import Definitions.Def_ShadowTomography_QuantumLB_sigmaState
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy

namespace P2MEntSigma

open ShadowTomography.QuantumLB Matrix

lemma sigma_eq {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (ε : ℝ) :
    sigmaState P ε = (((1 - 6 * ε) / N : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)
      + ((12 * ε / N : ℝ) : ℂ) • P := by
  unfold sigmaState rhoState
  rw [smul_smul, smul_smul]
  congr 2 <;> push_cast <;> ring

lemma herm_comb {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (hP : P.IsHermitian) (a b : ℝ) :
    ((a : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + (b : ℂ) • P).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hP.eq]
  simp [Complex.conj_ofReal]

lemma eig_two {N : ℕ} (P : Matrix (Fin N) (Fin N) ℂ) (hPP : P * P = P) (a b : ℝ)
    (hM : ((a : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + (b : ℂ) • P).IsHermitian) (j : Fin N) :
    hM.eigenvalues j = a ∨ hM.eigenvalues j = a + b := by
  have h1 := hM.mulVec_eigenvectorBasis j
  set v : Fin N → ℂ := ⇑(hM.eigenvectorBasis j) with hv
  set μ : ℝ := hM.eigenvalues j with hμ
  have hv0 : v ≠ 0 := by
    intro h
    apply (hM.eigenvectorBasis.orthonormal.ne_zero j)
    ext i
    simpa [hv] using congrFun h i
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h1
  have h1' : (a : ℂ) • v + (b : ℂ) • (P *ᵥ v) = (μ : ℂ) • v := by
    rw [h1]; rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]; rfl
  have h2 : (b : ℂ) • (P *ᵥ v) = ((μ : ℂ) - a) • v := by
    rw [sub_smul, ← h1']; abel
  have h3 : (b : ℂ) • (P *ᵥ v) = ((μ : ℂ) - a) • (P *ᵥ v) := by
    have := congrArg (fun w => P *ᵥ w) h2
    simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hPP] at this
    exact this
  have h4 : (((μ : ℂ) - a) * ((μ : ℂ) - a - b)) • v = 0 := by
    have e1 : ((μ : ℂ) - a) • ((b : ℂ) • (P *ᵥ v)) = ((μ : ℂ) - a) • (((μ : ℂ) - a) • v) := by
      rw [h2]
    have e2 : (b : ℂ) • ((b : ℂ) • (P *ᵥ v)) = (b : ℂ) • (((μ : ℂ) - a) • v) := by rw [h2]
    have e3 : (b : ℂ) • ((b : ℂ) • (P *ᵥ v)) = ((μ : ℂ) - a) • ((b : ℂ) • (P *ᵥ v)) := by
      conv_lhs => rw [h3]
      rw [smul_comm]
    have e4 : ((μ : ℂ) - a) • ((μ : ℂ) - a) • v = (b : ℂ) • ((μ : ℂ) - a) • v := by
      rw [← e1, ← e3, e2]
    rw [show ((μ : ℂ) - a) * ((μ : ℂ) - a - b)
        = ((μ : ℂ) - a) * ((μ : ℂ) - a) - (b : ℂ) * ((μ : ℂ) - a) by ring,
      sub_smul, mul_smul, mul_smul, e4, sub_self]
  rcases smul_eq_zero.mp h4 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · left; exact_mod_cast sub_eq_zero.mp h
    · right
      have : (μ : ℂ) = a + b := by linear_combination h
      exact_mod_cast this
  · exact absurd h hv0

lemma sum_two {N : ℕ} (lam : Fin N → ℝ) (a b : ℝ) (f : ℝ → ℝ)
    (hl : ∀ x, lam x = a ∨ lam x = a + b) (hs : ∑ x, lam x = N * a + (N / 2) * b) :
    ∑ x, f (lam x) = (N / 2) * (f a + f (a + b)) := by
  by_cases hb : b = 0
  · subst hb
    have : ∀ x, lam x = a := fun x => by rcases hl x with h | h <;> simpa using h
    simp [this]; ring
  · have hx : ∀ x, f (lam x) = f a + (lam x - a) / b * (f (a + b) - f a) := by
      intro x
      rcases hl x with h | h
      · rw [h]; simp
      · rw [h]; field_simp; ring
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_div, Finset.sum_sub_distrib, hs]
    simp
    field_simp
    ring

lemma xlogb (x d : ℝ) (hd : 0 < d) :
    (x / d) * Real.logb 2 (x / d) = (x / d) * (Real.logb 2 x - Real.logb 2 d) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.logb_div hx hd.ne']

end P2MEntSigma

open ShadowTomography.QuantumLB in
theorem solution {N : ℕ} (hN : 2 ≤ N) (P : Matrix (Fin N) (Fin N) ℂ)
    (hP : IsHalfProjector P) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 6) :
    vnEntropy (sigmaState P ε)
      = Real.logb 2 N
        - (1 - (1 / 2 + 3 * ε) * Real.logb 2 (1 / (1 / 2 + 3 * ε))
             - (1 / 2 - 3 * ε) * Real.logb 2 (1 / (1 / 2 - 3 * ε))) := by
  obtain ⟨hH, hPP, hT⟩ := hP
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  set a : ℝ := (1 - 6 * ε) / N with ha
  set b : ℝ := 12 * ε / N with hb
  have hM := P2MEntSigma.herm_comb P hH a b
  rw [P2MEntSigma.sigma_eq]
  unfold vnEntropy
  rw [dif_pos hM]
  have hl := P2MEntSigma.eig_two P hPP a b hM
  have hs : ∑ x, hM.eigenvalues x = N * a + (N / 2) * b := by
    have ht := hM.trace_eq_sum_eigenvalues
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, hT,
      Fintype.card_fin] at ht
    have hre := congrArg Complex.re ht
    simp at hre
    linear_combination -hre
  rw [P2MEntSigma.sum_two _ a b (fun t => t * Real.logb 2 t) hl hs]
  have hab : a + b = (1 + 6 * ε) / N := by rw [ha, hb]; field_simp; ring
  rw [hab, ha, P2MEntSigma.xlogb _ _ hNpos, P2MEntSigma.xlogb _ _ hNpos]
  have hp : (1 / 2 + 3 * ε) * Real.logb 2 (1 / (1 / 2 + 3 * ε))
      = - ((1 + 6 * ε) / 2) * (Real.logb 2 (1 + 6 * ε) - 1) := by
    have h1 : (1 / (1 / 2 + 3 * ε)) = 2 / (1 + 6 * ε) := by
      field_simp; ring
    rw [h1, Real.logb_div (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)]
    ring
  have hq : (1 / 2 - 3 * ε) * Real.logb 2 (1 / (1 / 2 - 3 * ε))
      = - ((1 - 6 * ε) / 2) * (Real.logb 2 (1 - 6 * ε) - 1) := by
    by_cases h0 : 1 - 6 * ε = 0
    · have : (1 / 2 - 3 * ε) = 0 := by linarith
      rw [this, h0]; simp
    · have h1 : (1 / (1 / 2 - 3 * ε)) = 2 / (1 - 6 * ε) := by
        field_simp; ring
      rw [h1, Real.logb_div (by norm_num) h0, Real.logb_self_eq_one (by norm_num)]
      ring
  rw [hp, hq]
  field_simp
  ring
