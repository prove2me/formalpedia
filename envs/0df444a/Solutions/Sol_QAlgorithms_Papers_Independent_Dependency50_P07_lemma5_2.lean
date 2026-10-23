-- Prove2me | solution 2 for QAlgorithms.Papers.Independent.Dependency50.P07.lemma5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:07:39.924522+00:00
-- url     : https://prove2.me/submissions/63fd49cf-b5d9-439e-beb4-e3185e9e2dbd

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

namespace X7F13

lemma X7F_gibbs_term (l q : ℝ) (hl : 0 ≤ l) (hq : 0 < q) :
    -(l * Real.log l) ≤ -(l * Real.log q) + (q - l) := by
  rcases hl.eq_or_lt with h | h
  · subst h; simp; linarith
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < q / l by positivity)
    rw [Real.log_div hq.ne' h.ne'] at h1
    have h2 : l * (q / l - 1) = q - l := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 h.le]

lemma X7F_log_interp (b t : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (ht : 0 < t) :
    (1 - b) * Real.log t + b * Real.log (1 + t) ≤ Real.log (b + t) := by
  have := (strictConcaveOn_log_Ioi.concaveOn).2 (show t ∈ Set.Ioi (0:ℝ) from ht)
    (show 1 + t ∈ Set.Ioi (0:ℝ) by simp; linarith) (by linarith : (0:ℝ) ≤ 1 - b) hb0 (by ring)
  simp only [smul_eq_mul] at this
  rw [show b + t = (1 - b) * t + b * (1 + t) by ring]; exact this

lemma X7F_classical {n : Type*} [Fintype n] [Nonempty n] (l b : n → ℝ) (hl0 : ∀ i, 0 ≤ l i)
    (hl1 : ∑ i, l i = 1) (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) (ε : ℝ)
    (hp : ∑ i, l i * b i = 1 - ε) :
    -∑ i, l i * Real.logb 2 (l i) ≤
      1 + ε * Real.logb 2 (Fintype.card n) + (1 - ε) * Real.logb 2 (∑ i, b i + 1) := by
  set β := ∑ i, b i with hβ
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun i _ => hb0 i
  set D : ℝ := (Fintype.card n : ℝ) with hD
  have hDpos : 0 < D := by rw [hD]; exact_mod_cast Fintype.card_pos
  set t := (β + 1) / D with ht
  have htpos : 0 < t := by positivity
  set Z := 2 * β + 1 with hZ
  have hZpos : 0 < Z := by positivity
  have htD : t * D = β + 1 := by rw [ht]; field_simp
  have hε1 : 0 ≤ 1 - ε := hp ▸ Finset.sum_nonneg fun i _ => mul_nonneg (hl0 i) (hb0 i)
  have hq : ∀ i, 0 < (b i + t) / Z := fun i => div_pos (by linarith [hb0 i]) hZpos
  have hsq : ∑ i, (b i + t) / Z = 1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hβ, ← hD, mul_comm, htD, hZ]; field_simp; ring
  -- natural-log bound
  have key : -∑ i, l i * Real.log (l i) ≤
      Real.log Z - ε * Real.log t - (1 - ε) * Real.log (1 + t) := by
    have h1 : ∀ i, -(l i * Real.log (l i)) ≤
        l i * Real.log Z - l i * ((1 - b i) * Real.log t + b i * Real.log (1 + t)) +
          ((b i + t) / Z - l i) := by
      intro i
      have g := X7F_gibbs_term (l i) _ (hl0 i) (hq i)
      rw [Real.log_div (by linarith [hb0 i]) hZpos.ne'] at g
      have c := mul_le_mul_of_nonneg_left (X7F_log_interp (b i) t (hb0 i) (hb1 i) htpos) (hl0 i)
      nlinarith
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
    rw [Finset.sum_neg_distrib] at h2
    refine h2.trans (le_of_eq ?_)
    have e1 : ∑ i, (l i * Real.log Z - l i * ((1 - b i) * Real.log t + b i * Real.log (1 + t)) +
          ((b i + t) / Z - l i)) = (∑ i, l i) * Real.log Z - ((∑ i, l i) - ∑ i, l i * b i) *
            Real.log t - (∑ i, l i * b i) * Real.log (1 + t) + ((∑ i, (b i + t) / Z) - ∑ i, l i) := by
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => show
        l i * Real.log Z - l i * ((1 - b i) * Real.log t + b i * Real.log (1 + t)) +
          ((b i + t) / Z - l i) = l i * Real.log Z - l i * Real.log t + l i * b i * Real.log t -
            l i * b i * Real.log (1 + t) + (b i + t) / Z - l i by ring]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    rw [e1, hl1, hp, hsq]; ring
  have hlogt : Real.log t = Real.log (β + 1) - Real.log D := by
    rw [ht, Real.log_div (by linarith) hDpos.ne']
  have hlog1t : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hlogZ : Real.log Z ≤ Real.log 2 + Real.log (β + 1) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log hZpos (by linarith)
  have key2 : -∑ i, l i * Real.log (l i) ≤
      Real.log 2 + ε * Real.log D + (1 - ε) * Real.log (β + 1) := by
    have := mul_nonneg hε1 hlog1t
    rw [hlogt] at key; nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.logb]
  have e : -∑ i, l i * (Real.log (l i) / Real.log 2) = (-∑ i, l i * Real.log (l i)) / Real.log 2 := by
    rw [neg_div, Finset.sum_div]; congr 1; refine Finset.sum_congr rfl fun i _ => by ring
  rw [e, div_le_iff₀ hl2]
  have : (1 + ε * (Real.log D / Real.log 2) + (1 - ε) * (Real.log (β + 1) / Real.log 2)) *
      Real.log 2 = Real.log 2 + ε * Real.log D + (1 - ε) * Real.log (β + 1) := by
    field_simp
  rw [this]; exact key2


open Matrix in
lemma X7F_reduce {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (sigma B : Matrix Q Q ℂ) (hsigma : IsDensityMatrix sigma) (hB : IsEffect B)
    (epsilon : ℝ) (htrace : (sigma * B).trace.re = 1 - epsilon) :
    vnEntropy sigma ≤ 1 + epsilon * Real.logb 2 (Fintype.card Q) +
      (1 - epsilon) * Real.logb 2 (B.trace.re + 1) := by
  have H : sigma.IsHermitian := hsigma.1.isHermitian
  set μ := H.eigenvalues with hμdef
  set U : Matrix Q Q ℂ := (H.eigenvectorUnitary : Matrix Q Q ℂ) with hUdef
  have hspec : sigma = U * diagonal (fun a => (μ a : ℂ)) * star U := by
    have := H.spectral_theorem
    simpa [Function.comp_def, hUdef, hμdef] using this
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self H.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self H.eigenvectorUnitary
  have hμ0 : ∀ a, 0 ≤ μ a := fun a => hsigma.1.eigenvalues_nonneg a
  have hμ1 : ∑ a, μ a = 1 := by
    have := H.trace_eq_sum_eigenvalues
    rw [hsigma.2] at this
    have := congrArg Complex.re this
    simpa using this.symm
  have hS : vnEntropy sigma = -(∑ a, μ a * Real.logb 2 (μ a)) := by
    rw [vnEntropy, H.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [show (star (H.eigenvectorUnitary : unitary (Matrix Q Q ℂ)) : Matrix Q Q ℂ) *
        (H.eigenvectorUnitary : Matrix Q Q ℂ) = 1 from
        Unitary.coe_star_mul_self H.eigenvectorUnitary, Matrix.one_mul, Matrix.trace_diagonal]
    simp [Function.comp_def, hμdef]
  set C : Matrix Q Q ℂ := star U * B * U with hC
  have hCpsd : C.PosSemidef := by
    have := hB.1.conjTranspose_mul_mul_same U
    simpa [hC, Matrix.star_eq_conjTranspose] using this
  have hC1psd : (1 - C).PosSemidef := by
    have := hB.2.conjTranspose_mul_mul_same U
    have e : Uᴴ * (1 - B) * U = 1 - C := by
      rw [hC, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hUU]
    rwa [e] at this
  have hb0 : ∀ i, 0 ≤ (C i i).re := fun i => (Complex.nonneg_iff.1 hCpsd.diag_nonneg).1
  have hb1 : ∀ i, (C i i).re ≤ 1 := by
    intro i
    have := (Complex.nonneg_iff.1 (hC1psd.diag_nonneg (i := i))).1
    simp [Matrix.sub_apply] at this
    linarith
  have hsumb : ∑ i, (C i i).re = B.trace.re := by
    have : C.trace = B.trace := by
      rw [hC, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [← this, Matrix.trace, Complex.re_sum]; rfl
  have hp : ∑ i, μ i * (C i i).re = 1 - epsilon := by
    rw [← htrace, hspec]
    have : (U * diagonal (fun a => (μ a : ℂ)) * star U * B).trace =
        (diagonal (fun a => (μ a : ℂ)) * C).trace := by
      rw [hC, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [this, Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.diagonal_mul]
  rw [hS, ← hsumb]
  exact X7F_classical μ (fun i => (C i i).re) hμ0 hμ1 hb0 hb1 epsilon hp

end X7F13

end

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P07 in
theorem solution {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (sigma B : Matrix Q Q ℂ) (hsigma : IsDensityMatrix sigma) (hB : IsEffect B)
    (epsilon : ℝ) (htrace : (sigma * B).trace.re = 1 - epsilon) :
    vnEntropy sigma ≤ 1 + epsilon * Real.logb 2 (Fintype.card Q) +
      (1 - epsilon) * Real.logb 2 (B.trace.re + 1) :=
  X7F13.X7F_reduce sigma B hsigma hB epsilon htrace

end
