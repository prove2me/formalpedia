-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P50.lemma_27
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:23:21.80784+00:00
-- url     : https://prove2.me/submissions/2c3db808-61e0-4683-8408-fbdf012b9683

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50
noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set



attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Bridge50.P50

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)





lemma l27_cont {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma l27_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma l27_eig_le_one {I : Type*} [Fintype I] [DecidableEq I] {rho : Mat I}
    (h : QAlgorithms.IsDensityMatrix rho) (hH : rho.IsHermitian) (i : I) :
    0 ≤ hH.eigenvalues i ∧ hH.eigenvalues i ≤ 1 := by
  have h0 : ∀ j, 0 ≤ hH.eigenvalues j := fun j => h.1.eigenvalues_nonneg j
  refine ⟨h0 i, ?_⟩
  have htr := hH.trace_eq_sum_eigenvalues
  rw [h.2] at htr
  have hs : ∑ j, hH.eigenvalues j = 1 := by
    have := congrArg Complex.re htr
    simpa using this.symm
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

/-- Tr(ρ C C) ≥ 0 for ρ PSD, C Hermitian. -/
lemma l27_tr_sq_nonneg {I : Type*} [Fintype I] [DecidableEq I] {rho C : Matrix I I ℂ}
    (hr : rho.PosSemidef) (hC : C.IsHermitian) : 0 ≤ (rho * (C * C)).trace.re := by
  have h1 : (rho * (C * C)).trace = (C.conjTranspose * rho * C).trace := by
    rw [hC.eq, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  have h2 := (hr.conjTranspose_mul_mul_same C).trace_nonneg
  rw [h1]
  exact (Complex.nonneg_iff.mp h2).1

lemma l27_rlog (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : r * Real.log r ^ 2 ≤ 4 := by
  rcases h0.lt_or_eq with h0 | h0
  · have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr h0
    have hs1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr h1
    have hl := Real.abs_log_mul_self_lt _ hs0 hs1
    have hlog : Real.log r = 2 * Real.log (Real.sqrt r) := by
      rw [Real.log_sqrt h0.le]; ring
    have hr : r = Real.sqrt r * Real.sqrt r := (Real.mul_self_sqrt h0.le).symm
    have : (Real.log (Real.sqrt r) * Real.sqrt r) ^ 2 < 1 := by
      have := abs_lt.mp hl; nlinarith
    calc r * Real.log r ^ 2 = 4 * (Real.log (Real.sqrt r) * Real.sqrt r) ^ 2 := by
          rw [hlog]; nth_rewrite 1 [hr]; ring
      _ ≤ 4 := by nlinarith
  · subst h0; simp

open QAlgorithms.Papers.Independent.Information100.P80 (log2) in
lemma l27_rho_part {I : Type*} [Fintype I] [DecidableEq I] {rho : Mat I}
    (h : QAlgorithms.IsDensityMatrix rho) :
    (rho * (cfc log2 rho * cfc log2 rho)).trace.re ≤ Fintype.card I * (4 / Real.log 2 ^ 2) := by
  have hH : rho.IsHermitian := h.1.isHermitian
  have e : rho * (cfc log2 rho * cfc log2 rho) = cfc (fun x => x * (log2 x * log2 x)) rho := by
    rw [cfc_mul (fun x => x) (fun x => log2 x * log2 x) rho (l27_cont _ _) (l27_cont _ _),
      cfc_mul log2 log2 rho (l27_cont _ _) (l27_cont _ _), cfc_id' ℝ rho]
  rw [e, l27_cfc_trace hH, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc ∑ i, hH.eigenvalues i * (log2 (hH.eigenvalues i) * log2 (hH.eigenvalues i))
      ≤ ∑ _i : I, 4 / Real.log 2 ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        obtain ⟨a, b⟩ := l27_eig_le_one h hH i
        have := l27_rlog _ a b
        simp only [log2]
        rw [le_div_iff₀ (by positivity)]
        field_simp
        nlinarith
    _ = _ := by simp

lemma l27_eig_ge {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {sigma : Mat I}
    (hH : sigma.IsHermitian) (i : I) : minEigenvalue sigma ≤ hH.eigenvalues i := by
  have hc : 0 < Fintype.card I := Fintype.card_pos
  unfold minEigenvalue QAlgorithms.ascEigenvalues
  rw [dif_pos hc, dif_pos hH]
  unfold Matrix.IsHermitian.eigenvalues
  apply hH.eigenvalues₀_antitone
  have := ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card I))).symm i).isLt
  rw [Fin.le_def, Fin.val_rev]
  show _ ≤ Fintype.card I - (0 + 1)
  omega

open QAlgorithms.Papers.Independent.Information100.P80 (log2) in
lemma l27_sigma_part {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {rho sigma : Mat I}
    (h : QAlgorithms.IsDensityMatrix rho) (hs : QAlgorithms.IsDensityMatrix sigma)
    (l0 : ℝ) (hl0 : 0 < l0) (hmin : l0 ≤ minEigenvalue sigma) :
    (rho * (cfc log2 sigma * cfc log2 sigma)).trace.re ≤ log2 l0 ^ 2 := by
  have hH : sigma.IsHermitian := hs.1.isHermitian
  set c := log2 l0 ^ 2 with hc
  have hspec : ∀ x ∈ spectrum ℝ sigma, log2 x ^ 2 ≤ c := by
    intro x hx
    rw [hH.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have h1 := (l27_eig_le_one hs hH i).2
    have h2 := hmin.trans (l27_eig_ge hH i)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have a1 : Real.log l0 ≤ Real.log (hH.eigenvalues i) := Real.log_le_log hl0 h2
    have a2 : Real.log (hH.eigenvalues i) ≤ 0 := Real.log_nonpos (hl0.le.trans h2) h1
    simp only [hc, log2, div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  set C := cfc (fun x => Real.sqrt (c - log2 x ^ 2)) sigma
  have hCC : C * C = algebraMap ℝ (Mat I) c - cfc log2 sigma * cfc log2 sigma := by
    rw [← cfc_mul _ _ sigma (l27_cont _ _) (l27_cont _ _), ← cfc_mul _ _ sigma (l27_cont _ _) (l27_cont _ _),
      ← cfc_const c sigma, ← cfc_sub _ _ sigma (l27_cont _ _) (l27_cont _ _)]
    apply cfc_congr
    intro x hx
    have := hspec x hx
    simp only
    rw [Real.mul_self_sqrt (by linarith)]
    ring
  have hCH : C.IsHermitian := (cfc_predicate _ sigma : IsSelfAdjoint C)
  have hnn := l27_tr_sq_nonneg h.1 hCH
  rw [hCC, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, Algebra.algebraMap_eq_smul_one,
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, h.2] at hnn
  simp at hnn
  linarith

open QAlgorithms.Papers.Independent.Information100.P80 (log2) in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ∀ rho ∈ S, QAlgorithms.IsDensityMatrix rho)
    (l0 : ℝ) (hl0 : 0 < l0) :
    ∃ V : ℝ, ∀ rho ∈ S, ∀ sigma : Mat I, QAlgorithms.IsDensityMatrix sigma →
      l0 ≤ minEigenvalue sigma → pairInformationVariance rho sigma ≤ V := by
  refine ⟨2 * (Fintype.card I * (4 / Real.log 2 ^ 2)) + 2 * log2 l0 ^ 2, ?_⟩
  intro rho hrho sigma hs hmin
  have h := hS rho hrho
  unfold pairInformationVariance
  simp only
  have h1 := l27_rho_part h
  have h2 := l27_sigma_part h hs l0 hl0 hmin
  set A := cfc log2 rho
  set B := cfc log2 sigma
  have hAB : (A - B) * (A - B) = 2 • (A * A) + 2 • (B * B) - (A + B) * (A + B) := by noncomm_ring
  have hApB : (A + B).IsHermitian := by
    have hA : A.IsHermitian := (cfc_predicate _ rho : IsSelfAdjoint A)
    have hB : B.IsHermitian := (cfc_predicate _ sigma : IsSelfAdjoint B)
    exact hA.add hB
  have hn := l27_tr_sq_nonneg h.1 hApB
  rw [hAB, Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
  simp only [Complex.sub_re, Complex.add_re, nsmul_eq_mul, Nat.cast_ofNat]
  simp only [nsmul_eq_mul] at *
  have := sq_nonneg (QAlgorithms.Papers.Independent.Dependency50.P36.relativeEntropyFinite rho sigma)
  have e2 : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp
  rw [e2, e2]
  linarith
