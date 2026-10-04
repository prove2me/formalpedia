-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.relEntropy_nonneg_and_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T20:45:04.494768+00:00
-- url     : https://prove2.me/submissions/41fba7a4-5a90-4891-8b06-554821d7b9cd

import Definitions.Def_pme_quantum_basics

private lemma klein_scalar (p s : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hsupp : p ≠ 0 → s ≠ 0) :
    0 ≤ p * (Real.log p - Real.log s) - p + s ∧
      (p * (Real.log p - Real.log s) - p + s = 0 ↔ p = s) := by
  by_cases hp0 : p = 0
  · simp only [hp0, zero_mul, sub_zero, zero_add]
    exact ⟨hs, eq_comm⟩
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hs0 : s ≠ 0 := hsupp hp0
  have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hlog : Real.log (s / p) = Real.log s - Real.log p := Real.log_div hs0 hp0
  have hle := Real.log_le_sub_one_of_pos (div_pos hsp hpp)
  have hmul : p * Real.log (s / p) ≤ s - p := by
    have h := (mul_le_mul_of_nonneg_left hle hp)
    have hcancel : p * (s / p - 1) = s - p := by field_simp
    rwa [hcancel] at h
  refine ⟨?_, ?_⟩
  · rw [hlog] at hmul
    nlinarith
  · constructor
    · intro hz
      by_contra hne
      have hratio : s / p ≠ 1 := by
        intro h
        have heq := (div_eq_one_iff_eq hp0).mp h
        exact hne heq.symm
      have hlt := Real.log_lt_sub_one_of_pos (div_pos hsp hpp) hratio
      have h := mul_lt_mul_of_pos_left hlt hpp
      have hcancel : p * (s / p - 1) = s - p := by field_simp
      rw [hcancel, hlog] at h
      nlinarith
    · intro heq
      subst s
      ring

private lemma klein_weighted {n : Type} [Fintype n] (p s : n → ℝ)
    (w : n → n → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∀ j, 0 ≤ s j)
    (hw : ∀ i j, 0 ≤ w i j)
    (hsupp : ∀ i j, w i j ≠ 0 → p i ≠ 0 → s j ≠ 0) :
    0 ≤ ∑ i, ∑ j, w i j * (p i * (Real.log (p i) - Real.log (s j)) - p i + s j) ∧
    ((∑ i, ∑ j, w i j * (p i * (Real.log (p i) - Real.log (s j)) - p i + s j)) = 0 ↔
      ∀ i j, w i j = 0 ∨ p i = s j) := by
  have hnonneg (i j : n) :
      0 ≤ w i j * (p i * (Real.log (p i) - Real.log (s j)) - p i + s j) := by
    by_cases h : w i j = 0
    · simp [h]
    · exact mul_nonneg (hw i j) (klein_scalar (p i) (s j) (hp i) (hs j) (hsupp i j h)).1
  refine ⟨Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnonneg i j)), ?_⟩
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hnonneg i j))]
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · intro h i j
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg i j)).mp (h i) j
      (Finset.mem_univ j)
    by_cases hw0 : w i j = 0
    · exact Or.inl hw0
    · exact Or.inr ((klein_scalar (p i) (s j) (hp i) (hs j) (hsupp i j hw0)).2.mp
        ((mul_eq_zero.mp hz).resolve_left hw0))
  · intro h i
    apply Finset.sum_eq_zero
    intro j _
    obtain hw0 | heq := h i j
    · simp [hw0]
    · rw [heq]
      ring

open Matrix

private lemma trace_weight {n : Type} [Fintype n] [DecidableEq n]
    (p s : n → ℝ) (W : Matrix n n ℂ) :
    (diagonal (fun i => (p i : ℂ)) * (W * diagonal (fun j => (s j : ℂ)) * Wᴴ)).trace.re =
      ∑ i, ∑ j, p i * s j * Complex.normSq (W i j) := by
  change (∑ i, (diagonal (fun i => (p i : ℂ)) *
    (W * diagonal (fun j => (s j : ℂ)) * Wᴴ)) i i).re = _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonal_mul, Matrix.mul_apply]
  simp only [mul_diagonal, Matrix.conjTranspose_apply, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq]
  ring

open ProjectiveMeasurementEquilibration

private lemma matrix_klein {n : Type} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℂ) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hsupp : SupportLE ρ σ) :
    0 ≤ (ρ * (matrixLog ρ - matrixLog σ)).trace.re ∧
    ((ρ * (matrixLog ρ - matrixLog σ)).trace.re = 0 ↔ ρ = σ) := by
  classical
  let p := hρ.1.1.eigenvalues
  let s := hσ.1.1.eigenvalues
  let U := hρ.1.1.eigenvectorUnitary
  let V := hσ.1.1.eigenvectorUnitary
  let W := star U * V
  let w : Matrix n n ℂ := W
  let G := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  let F := G.symm
  have hp (i : n) : 0 ≤ p i := hρ.1.eigenvalues_nonneg i
  have hs (j : n) : 0 ≤ s j := hσ.1.eigenvalues_nonneg j
  have htrace (A : Matrix n n ℂ) : (F A).trace = A.trace := by
    change (star (U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)).trace = A.trace
    rw [Matrix.trace_mul_cycle, Unitary.mul_star_self_of_mem U.property, one_mul]
  have hFp : F ρ = diagonal (fun i => (p i : ℂ)) := by
    simpa [F, G, U, p, Function.comp_def] using hρ.1.1.conjStarAlgAut_star_eigenvectorUnitary
  have hconj (d : n → ℂ) :
      F (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) V (diagonal d)) =
        w * diagonal d * wᴴ := by
    simp only [F, G, Unitary.conjStarAlgAut_symm_apply, Unitary.conjStarAlgAut_apply,
      w, W, Submonoid.coe_mul, Unitary.coe_star, star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc]
  have hFσ : F σ = w * diagonal (fun j => (s j : ℂ)) * wᴴ := by
    rw [hσ.1.1.spectral_theorem]
    exact hconj _
  have hFlp : F (matrixLog ρ) = diagonal (fun i => (Real.log (p i) : ℂ)) := by
    rw [matrixLog, hρ.1.1.cfc_eq]
    change G.symm (G _) = _
    rw [G.symm_apply_apply]
    rfl
  have hFls : F (matrixLog σ) = w * diagonal (fun j => (Real.log (s j) : ℂ)) * wᴴ := by
    rw [matrixLog, hσ.1.1.cfc_eq]
    exact hconj _
  have hrows (i : n) : ∑ j, Complex.normSq (w i j) = 1 := by
    have h := congrArg (fun A : Matrix n n ℂ => (A i i).re) (Unitary.coe_mul_star_self W)
    simpa [w, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_conj] using h
  have hcols (j : n) : ∑ i, Complex.normSq (w i j) = 1 := by
    have h := congrArg (fun A : Matrix n n ℂ => (A j j).re) (Unitary.coe_star_mul_self W)
    simpa [w, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      Complex.normSq, pow_two] using h
  have hpsum : ∑ i, p i = 1 := by
    have h := congrArg Complex.re hρ.2
    rw [← htrace ρ, hFp] at h
    simpa [Matrix.trace_diagonal, Complex.re_sum] using h
  have hssum : ∑ j, s j = 1 := by
    have h := congrArg Complex.re hσ.2
    rw [hσ.1.1.trace_eq_sum_eigenvalues] at h
    simpa using h
  have hpp : (ρ * matrixLog ρ).trace.re = ∑ i, p i * Real.log (p i) := by
    rw [← htrace (ρ * matrixLog ρ), map_mul, hFp, hFlp, diagonal_mul_diagonal]
    simp [Matrix.trace_diagonal, Complex.re_sum]
  have hps : (ρ * matrixLog σ).trace.re =
      ∑ i, ∑ j, p i * Real.log (s j) * Complex.normSq (w i j) := by
    rw [← htrace (ρ * matrixLog σ), map_mul, hFp, hFls]
    exact trace_weight _ _ _
  have hσV : σ * (V : Matrix n n ℂ) = (V : Matrix n n ℂ) * diagonal (fun j => (s j : ℂ)) := by
    rw [hσ.1.1.spectral_theorem]
    change ((V : Matrix n n ℂ) * diagonal (fun j => (s j : ℂ)) * star (V : Matrix n n ℂ)) * V = _
    rw [mul_assoc, Unitary.star_mul_self_of_mem V.property, mul_one]
  have hprod : star (U : Matrix n n ℂ) * ρ * (V : Matrix n n ℂ) =
      diagonal (fun i => (p i : ℂ)) * w := by
    rw [← hFp]
    change star (U : Matrix n n ℂ) * ρ * (V : Matrix n n ℂ) =
      (star (U : Matrix n n ℂ) * ρ * U) * (star (U : Matrix n n ℂ) * V)
    symm
    calc
      _ = star (U : Matrix n n ℂ) * ρ * ((U : Matrix n n ℂ) * star (U : Matrix n n ℂ)) * V := by
        simp only [mul_assoc]
      _ = _ := by rw [Unitary.mul_star_self_of_mem U.property, mul_one]
  have hsupport (i j : n) (hw : Complex.normSq (w i j) ≠ 0) (hpi : p i ≠ 0) : s j ≠ 0 := by
    intro hsj
    have hvσ : σ *ᵥ ((V : Matrix n n ℂ) *ᵥ Pi.single j 1) = 0 := by
      rw [mulVec_mulVec, hσV, ← mulVec_mulVec, diagonal_mulVec_single]
      simp [hsj]
    have hvρ := hsupp _ hvσ
    have hm : (diagonal (fun i => (p i : ℂ)) * w) *ᵥ Pi.single j 1 = 0 := by
      rw [← hprod, ← mulVec_mulVec, ← mulVec_mulVec, hvρ, mulVec_zero]
    have hi := congrFun hm i
    simp only [mulVec_single_one, Pi.zero_apply] at hi
    change (diagonal (fun i => (p i : ℂ)) * w) i j = 0 at hi
    rw [diagonal_mul] at hi
    have hw0 : w i j = 0 := (mul_eq_zero.mp hi).resolve_left (by exact_mod_cast hpi)
    exact hw (Complex.normSq_eq_zero.mpr hw0)
  have hrowconst (r : n → ℝ) :
      (∑ i, ∑ j, Complex.normSq (w i j) * r i) = ∑ i, r i := by
    simp_rw [mul_comm (Complex.normSq _) _, ← Finset.mul_sum, hrows, mul_one]
  have hcolconst (r : n → ℝ) :
      (∑ i, ∑ j, Complex.normSq (w i j) * r j) = ∑ j, r j := by
    rw [Finset.sum_comm]
    simp_rw [mul_comm (Complex.normSq _) _, ← Finset.mul_sum, hcols, mul_one]
  have hrepr :
      (∑ i, ∑ j, Complex.normSq (w i j) *
        (p i * (Real.log (p i) - Real.log (s j)) - p i + s j)) =
      (ρ * (matrixLog ρ - matrixLog σ)).trace.re := by
    have hexp (i j : n) : Complex.normSq (w i j) *
        (p i * (Real.log (p i) - Real.log (s j)) - p i + s j) =
        Complex.normSq (w i j) * (p i * Real.log (p i)) -
        p i * Real.log (s j) * Complex.normSq (w i j) -
        Complex.normSq (w i j) * p i + Complex.normSq (w i j) * s j := by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hrowconst, hrowconst, hcolconst, hpsum, hssum]
    rw [mul_sub, Matrix.trace_sub, Complex.sub_re, hpp, hps]
    ring
  have hklein := klein_weighted p s (fun i j => Complex.normSq (w i j)) hp hs
    (fun _ _ => Complex.normSq_nonneg _) hsupport
  refine ⟨hrepr ▸ hklein.1, ?_⟩
  constructor
  · intro hz
    have hc := hklein.2.mp (hrepr.trans hz)
    have hinter : diagonal (fun i => (p i : ℂ)) * w = w * diagonal (fun j => (s j : ℂ)) := by
      ext i j
      rw [diagonal_mul, mul_diagonal]
      obtain hw0 | heq := hc i j
      · rw [Complex.normSq_eq_zero.mp hw0]
        simp
      · rw [heq, mul_comm]
    apply F.injective
    change F ρ = F σ
    have hww : w * wᴴ = 1 := Unitary.mul_star_self_of_mem W.property
    rw [hFp, hFσ, ← hinter, mul_assoc, hww, mul_one]
  · intro heq
    subst σ
    simp

theorem solution {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    0 ≤ relEntropy ρ σ ∧ (relEntropy ρ σ = 0 ↔ ρ = σ) := by
  by_cases hsupp : SupportLE ρ σ
  · have hk := matrix_klein ρ σ hρ hσ hsupp
    rw [relEntropy, if_pos hsupp]
    constructor
    · exact_mod_cast hk.1
    · rw [← EReal.coe_zero, EReal.coe_eq_coe_iff]
      exact hk.2
  · rw [relEntropy, if_neg hsupp]
    refine ⟨le_top, ?_⟩
    constructor
    · intro h
      simp at h
    · intro heq
      subst σ
      exact False.elim (hsupp (fun _ hv => hv))
