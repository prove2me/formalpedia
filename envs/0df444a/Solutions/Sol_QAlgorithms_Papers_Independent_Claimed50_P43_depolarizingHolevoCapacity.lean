-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P43.depolarizingHolevoCapacity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:40:52.354502+00:00
-- url     : https://prove2.me/submissions/966b8746-197e-428e-9fcd-ff71d2361197

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43
noncomputable section
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X7DH

open QAlgorithms.Papers.Independent.Dependency50.P45 QAlgorithms.Papers.Independent.Claimed50.P43

attribute [local instance] Classical.propDecidable

lemma X7DH_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma X7DH_term_le (D μ : ℝ) (hD : 0 < D) (hμ : 0 ≤ μ) :
    -(μ * Real.log μ) - μ * Real.log D ≤ 1 / D - μ := by
  rcases hμ.eq_or_lt with h | h
  · subst h; simp; positivity
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (D * μ) by positivity)
    rw [one_div, Real.log_inv, Real.log_mul hD.ne' h.ne'] at h1
    have h2 : μ * ((D * μ)⁻¹ - 1) = 1 / D - μ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 h.le]

lemma X7DH_ent_le_log {n : Type*} [Fintype n] (μ : n → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hs : ∑ i, μ i = 1) (hn : 0 < Fintype.card n) :
    -∑ i, μ i * Real.logb 2 (μ i) ≤ Real.logb 2 (Fintype.card n) := by
  have hD : (0:ℝ) < Fintype.card n := by exact_mod_cast hn
  have key : ∑ i, (-(μ i * Real.log (μ i)) - μ i * Real.log (Fintype.card n)) ≤
      ∑ _i : n, (1 / (Fintype.card n : ℝ)) - ∑ i, μ i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => X7DH_term_le _ _ hD (hμ i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at key
  rw [mul_one_div_cancel hD.ne'] at key
  simp only [Real.logb, ← Finset.sum_neg_distrib]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : ∑ i, -(μ i * (Real.log (μ i) / Real.log 2)) = (∑ i, -(μ i * Real.log (μ i))) / Real.log 2 := by
    rw [Finset.sum_div]; congr 1; ext i; ring
  rw [this, div_le_div_iff_of_pos_right hl]
  linarith

lemma X7DH_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma X7DH_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := X7DH_diag_herm d
  rw [X7DH_cfc_trace hD]
  have h1 := hD.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma X7DH_vn_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [X7DH_trace_cfc_diag]
  simp

lemma X7DH_affine {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (a c : ℝ) : cfc (fun x : ℝ => a * x + c) ρ =
      ((c : ℝ) : ℂ) • (1 : Matrix n n ℂ) + ((a : ℝ) : ℂ) • ρ := by
  rw [cfc_add (a := ρ) (fun x : ℝ => a * x) (fun _ => c), cfc_const_mul_id a ρ hρ.isSelfAdjoint,
    cfc_const c ρ hρ.isSelfAdjoint, Algebra.algebraMap_eq_smul_one, add_comm]
  congr 1
  all_goals (ext i j; simp [Matrix.one_apply])

lemma X7DH_ent_comp {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (g : ℝ → ℝ) : vnEntropy (cfc g ρ) =
      -∑ i, g (hρ.eigenvalues i) * Real.logb 2 (g (hρ.eigenvalues i)) := by
  unfold vnEntropy
  rw [← cfc_comp (fun x : ℝ => x * Real.logb 2 x) g ρ hρ.isSelfAdjoint
    ((ρ.finite_real_spectrum.image _).continuousOn _) (ρ.finite_real_spectrum.continuousOn _),
    X7DH_cfc_trace hρ]
  simp [Complex.re_sum]

lemma X7DH_eig {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ)
    (hH : ρ.IsHermitian) : (∀ i, 0 ≤ hH.eigenvalues i) ∧ ∑ i, hH.eigenvalues i = 1 := by
  refine ⟨fun i => h.1.eigenvalues_nonneg i, ?_⟩
  have := hH.trace_eq_sum_eigenvalues
  rw [h.2] at this
  have h2 := congrArg Complex.re this
  simp at h2
  linarith

lemma X7DH_eig01 {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ} (h : IsDensityMatrix ρ)
    (hH : ρ.IsHermitian) (hsq : ρ * ρ = ρ) : ∀ i, hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := by
  obtain ⟨h0, hs⟩ := X7DH_eig h hH
  have h1 : ∀ i, hH.eigenvalues i ≤ 1 := fun i => by
    rw [← hs]; exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  have e : cfc (fun x : ℝ => x * x) ρ = ρ := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) ρ, cfc_id' ℝ ρ hH.isSelfAdjoint, hsq]
  have t := X7DH_cfc_trace hH (fun x : ℝ => x * x)
  rw [e, h.2] at t
  have t2 := congrArg Complex.re t
  simp only [Complex.re_sum, Complex.ofReal_re, Complex.one_re] at t2
  have hz : ∑ i, (hH.eigenvalues i - hH.eigenvalues i * hH.eigenvalues i) = 0 := by
    rw [Finset.sum_sub_distrib, hs, ← t2, sub_self]
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ hH.eigenvalues i - hH.eigenvalues i * hH.eigenvalues i :=
    fun i _ => by nlinarith [h0 i, h1 i]
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hz i (Finset.mem_univ _)
  have : hH.eigenvalues i * (1 - hH.eigenvalues i) = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by linarith)

lemma X7DH_conv (a c l : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ a + c) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    (a * l + c) * Real.logb 2 (a * l + c) ≤
      (1 - l) * (c * Real.logb 2 c) + l * ((a + c) * Real.logb 2 (a + c)) := by
  have h := Real.convexOn_mul_log.2 (Set.mem_Ici.2 hc) (Set.mem_Ici.2 hb) (sub_nonneg.2 hl1) hl0
    (by ring)
  simp only [smul_eq_mul] at h
  have e : (1 - l) * c + l * (a + c) = a * l + c := by ring
  rw [e] at h
  simp only [Real.logb]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e2 : ∀ x y : ℝ, x * (Real.log y / Real.log 2) = x * Real.log y / Real.log 2 :=
    fun x y => by ring
  simp only [e2, mul_div_assoc', ← add_div]
  rw [div_le_div_iff_of_pos_right hl2]
  linarith

lemma X7DH_conv_eq (a c l : ℝ) (hl : l = 0 ∨ l = 1) :
    (a * l + c) * Real.logb 2 (a * l + c) =
      (1 - l) * (c * Real.logb 2 c) + l * ((a + c) * Real.logb 2 (a + c)) := by
  rcases hl with rfl | rfl <;> simp

lemma X7DH_sum_rhs {n : Type*} [Fintype n] (l : n → ℝ) (hs : ∑ i, l i = 1) (X Y : ℝ) :
    ∑ i, ((1 - l i) * X + l i * Y) = ((Fintype.card n : ℝ) - 1) * X + Y := by
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib, hs]
  simp

lemma X7DH_sum_le {n : Type*} [Fintype n] (a c : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ a + c) (l : n → ℝ)
    (h0 : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1) :
    ∑ i, (a * l i + c) * Real.logb 2 (a * l i + c) ≤
      ((Fintype.card n : ℝ) - 1) * (c * Real.logb 2 c) + (a + c) * Real.logb 2 (a + c) := by
  have h1 : ∀ i, l i ≤ 1 := fun i => by
    rw [← hs]; exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  rw [← X7DH_sum_rhs l hs]
  exact Finset.sum_le_sum fun i _ => X7DH_conv a c (l i) hc hb (h0 i) (h1 i)

lemma X7DH_sum_eq {n : Type*} [Fintype n] (a c : ℝ) (l : n → ℝ)
    (h01 : ∀ i, l i = 0 ∨ l i = 1) (hs : ∑ i, l i = 1) :
    ∑ i, (a * l i + c) * Real.logb 2 (a * l i + c) =
      ((Fintype.card n : ℝ) - 1) * (c * Real.logb 2 c) + (a + c) * Real.logb 2 (a + c) := by
  rw [← X7DH_sum_rhs l hs]
  exact Finset.sum_congr rfl fun i _ => X7DH_conv_eq a c (l i) (h01 i)

variable {d : ℕ}

lemma X7DH_map_eq (hd : 0 < d) (p : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.IsHermitian)
    (htr : ρ.trace = 1) :
    QuditFidelity.depolarizingMap d hd p ρ = cfc (fun x : ℝ => (1 - p) * x + p / d) ρ := by
  rw [X7DH_affine hρ]
  simp only [QuditFidelity.depolarizingMap, htr, mul_one]

lemma X7DH_ent_out (hd : 0 < d) (p : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.IsHermitian)
    (htr : ρ.trace = 1) :
    vnEntropy (QuditFidelity.depolarizingMap d hd p ρ) =
      -∑ i, ((1 - p) * hρ.eigenvalues i + p / d) * Real.logb 2 ((1 - p) * hρ.eigenvalues i + p / d) := by
  rw [X7DH_map_eq hd p ρ hρ htr, X7DH_ent_comp hρ]

/-- minimal output entropy -/
def X7DH_Smin (d : ℕ) (p : ℝ) : ℝ :=
  -(((d : ℝ) - 1) * ((p / d) * Real.logb 2 (p / d)) + ((1 - p) + p / d) * Real.logb 2 ((1 - p) + p / d))

lemma X7DH_lower (hd : 0 < d) (p : ℝ) (hc : 0 ≤ p / d) (hb : 0 ≤ (1 - p) + p / d)
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : IsDensityMatrix σ) :
    X7DH_Smin d p ≤ vnEntropy (QuditFidelity.depolarizingMap d hd p σ) := by
  obtain ⟨h0, hs⟩ := X7DH_eig hσ hσ.1.isHermitian
  rw [X7DH_ent_out hd p σ hσ.1.isHermitian hσ.2]
  have := X7DH_sum_le (1 - p) (p / d) hc hb _ h0 hs
  rw [Fintype.card_fin] at this
  unfold X7DH_Smin
  linarith

lemma X7DH_pure (hd : 0 < d) (p : ℝ)
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : IsDensityMatrix σ) (hsq : σ * σ = σ) :
    vnEntropy (QuditFidelity.depolarizingMap d hd p σ) = X7DH_Smin d p := by
  obtain ⟨h0, hs⟩ := X7DH_eig hσ hσ.1.isHermitian
  rw [X7DH_ent_out hd p σ hσ.1.isHermitian hσ.2]
  have := X7DH_sum_eq (1 - p) (p / d) _ (X7DH_eig01 hσ hσ.1.isHermitian hsq) hs
  rw [Fintype.card_fin] at this
  unfold X7DH_Smin
  linarith

lemma X7DH_upper (hd : 0 < d) (p : ℝ) (hc : 0 ≤ p / d) (hb : 0 ≤ (1 - p) + p / d)
    (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : IsDensityMatrix σ) :
    vnEntropy (QuditFidelity.depolarizingMap d hd p σ) ≤ Real.logb 2 d := by
  obtain ⟨h0, hs⟩ := X7DH_eig hσ hσ.1.isHermitian
  have h1 : ∀ i, hσ.1.isHermitian.eigenvalues i ≤ 1 := fun i => by
    rw [← hs]; exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  rw [X7DH_ent_out hd p σ hσ.1.isHermitian hσ.2]
  have hdR : (d : ℝ) ≠ 0 := by have : (0:ℝ) < d := by exact_mod_cast hd
                               exact this.ne'
  have := X7DH_ent_le_log (fun i => (1 - p) * hσ.1.isHermitian.eigenvalues i + p / d)
    (fun i => by nlinarith [mul_nonneg (sub_nonneg.2 (h1 i)) hc, mul_nonneg (h0 i) hb])
    (by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have : (d : ℝ) * (p / d) = p := by field_simp
      linarith)
    (by simp; omega)
  simpa using this

lemma X7DH_avg {m : ℕ} (q : Fin m → ℝ) (rho : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) (hrho : ∀ j, IsDensityMatrix (rho j)) :
    IsDensityMatrix (∑ j, (q j : ℂ) • rho j) := by
  refine ⟨Matrix.posSemidef_sum _ fun j _ => (hrho j).1.smul (Complex.zero_le_real.2 (hq0 j)), ?_⟩
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_smul, (hrho _).2, smul_eq_mul, mul_one]
  exact_mod_cast hq1

lemma X7DH_col (U : Matrix (Fin d) (Fin d) ℂ) (j a : Fin d) : (act U (ket j)) a = U a j := by
  simp [act, ket, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]

lemma X7DH_col_density (U : Matrix.unitaryGroup (Fin d) ℂ) (j : Fin d) :
    IsDensityMatrix (pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket j))) ∧
    pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket j)) *
      pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket j)) =
      pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket j)) := by
  set u : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
  have h2 : star u * u = 1 := Unitary.star_mul_self_of_mem U.2
  have hcol : ∑ k, (starRingEnd ℂ) (u k j) * u k j = 1 := by
    have := congrFun (congrFun h2 j) j
    simpa [Matrix.mul_apply, Matrix.star_apply] using this
  have hpd : pureDensity (act u (ket j)) = Matrix.vecMulVec (WithLp.ofLp (act u (ket j)))
      (star (WithLp.ofLp (act u (ket j)))) := by
    ext a b; simp [pureDensity, Matrix.vecMulVec_apply]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hpd]; exact Matrix.posSemidef_vecMulVec_self_star _
  · simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply, X7DH_col]
    rw [← hcol]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · ext a b
    simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, X7DH_col]
    have : ∀ k, (u a j * (starRingEnd ℂ) (u k j)) * (u k j * (starRingEnd ℂ) (u b j)) =
        (u a j * (starRingEnd ℂ) (u b j)) * ((starRingEnd ℂ) (u k j) * u k j) := fun k => by ring
    simp_rw [this, ← Finset.mul_sum, hcol, mul_one]

lemma X7DH_col_sum (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ∑ j, pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (ket j)) = 1 := by
  set u : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
  have h1 : u * star u = 1 := Unitary.mul_star_self_of_mem U.2
  ext a b
  have := congrFun (congrFun h1 a) b
  simp only [Matrix.sum_apply, pureDensity, Matrix.of_apply, X7DH_col]
  rw [← this, Matrix.mul_apply]
  simp [Matrix.star_apply]

lemma X7DH_avg_ent (hd : 0 < d) (p : ℝ) :
    vnEntropy (QuditFidelity.depolarizingMap d hd p ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ))) =
      Real.logb 2 d := by
  have hdR : (d : ℝ) ≠ 0 := by have : (0:ℝ) < d := by exact_mod_cast hd
                               exact this.ne'
  have hN : QuditFidelity.depolarizingMap d hd p ((d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)) =
      Matrix.diagonal (fun _ : Fin d => (((d : ℝ)⁻¹ : ℝ) : ℂ)) := by
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdR
    ext i j
    simp only [QuditFidelity.depolarizingMap, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs
    · have hdC' : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hdR
      push_cast
      field_simp
      ring_nf
      have e1 : (d : ℂ) * (d : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hdC
      have e2 : (d : ℂ) ^ 2 * (d : ℂ)⁻¹ ^ 2 = 1 := by rw [← mul_pow, e1, one_pow]
      linear_combination (-(p : ℂ)) * e1 + e1 + (p : ℂ) * e2
    · simp
  rw [hN, X7DH_vn_diag]
  simp [Real.logb_inv]
  field_simp

lemma X7DH_basis (hd : 0 < d) (p : ℝ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    basisHolevo hd p U = Real.logb 2 d - X7DH_Smin d p := by
  unfold basisHolevo
  rw [X7DH_col_sum U, X7DH_avg_ent hd p]
  simp_rw [X7DH_pure hd p _ (X7DH_col_density U _).1 (X7DH_col_density U _).2]
  have hdR : (d : ℝ) ≠ 0 := by have : (0:ℝ) < d := by exact_mod_cast hd
                               exact this.ne'
  simp
  field_simp

theorem X7DH_main (d : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) :
    let N := QAlgorithms.QuditFidelity.depolarizingMap d (by omega) p
    let b := 1 - p * ((d : ℝ) - 1) / d
    holevoCapacity N = Real.logb 2 d + b * Real.logb 2 b +
      (p * ((d : ℝ) - 1) / d) * Real.logb 2 (p / d) ∧
    ∀ U : Matrix.unitaryGroup (Fin d) ℂ, basisHolevo (by omega) p U = holevoCapacity N := by
  intro N b
  have hd0 : 0 < d := by omega
  have hdR2 : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hc : 0 ≤ p / d := by positivity
  have hbe : b = (1 - p) + p / d := by
    show 1 - p * ((d:ℝ) - 1) / d = (1 - p) + p / d
    field_simp; ring
  have hq : 0 < (d:ℝ)^2 - 1 := by nlinarith
  have h1 : p * ((d:ℝ)^2 - 1) ≤ (d:ℝ)^2 := by rwa [le_div_iff₀ hq] at hp1
  have h2 : p * ((d:ℝ) - 1) ≤ d := by nlinarith
  have hb : 0 ≤ (1 - p) + p / d := by
    rw [← hbe]
    show 0 ≤ 1 - p * ((d:ℝ) - 1) / d
    have : p * ((d:ℝ) - 1) / d ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h2
    linarith
  have hV : Real.logb 2 d + b * Real.logb 2 b + (p * ((d : ℝ) - 1) / d) * Real.logb 2 (p / d) =
      Real.logb 2 d - X7DH_Smin d p := by
    rw [hbe]; unfold X7DH_Smin; ring
  have hcap : holevoCapacity N = Real.logb 2 d - X7DH_Smin d p := by
    unfold holevoCapacity
    apply IsGreatest.csSup_eq
    refine ⟨⟨d, fun _ => (d : ℝ)⁻¹, fun j => pureDensity (act ((1 : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) (ket j)), fun _ => by positivity, ?_,
        fun j => (X7DH_col_density 1 j).1, ?_⟩, ?_⟩
    · simp; field_simp
    · rw [← X7DH_basis hd0 p 1]
      unfold basisHolevo
      rw [← Finset.mul_sum, ← Finset.smul_sum]
      push_cast
      rfl
    · rintro v ⟨m, q, rho, hq0, hq1, hrho, rfl⟩
      have hu := X7DH_upper hd0 p hc hb _ (X7DH_avg q rho hq0 hq1 hrho)
      have hl : ∑ j, q j * X7DH_Smin d p ≤ ∑ j, q j * vnEntropy (N (rho j)) :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (X7DH_lower hd0 p hc hb _ (hrho j)) (hq0 j)
      rw [← Finset.sum_mul, hq1, one_mul] at hl
      linarith
  refine ⟨hcap.trans hV.symm, fun U => ?_⟩
  rw [hcap]
  exact X7DH_basis hd0 p U

end X7DH

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P45 QAlgorithms.Papers.Independent.Claimed50.P43 in
attribute [local instance] Classical.propDecidable in
theorem solution (d : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ (d : ℝ)^2 / ((d : ℝ)^2 - 1)) :
    let N := QAlgorithms.QuditFidelity.depolarizingMap d (by omega) p
    let b := 1 - p * ((d : ℝ) - 1) / d
    holevoCapacity N = Real.logb 2 d + b * Real.logb 2 b +
      (p * ((d : ℝ) - 1) / d) * Real.logb 2 (p / d) ∧
    ∀ U : Matrix.unitaryGroup (Fin d) ℂ, basisHolevo (by omega) p U = holevoCapacity N :=
  X7DH.X7DH_main d hd p hp0 hp1
