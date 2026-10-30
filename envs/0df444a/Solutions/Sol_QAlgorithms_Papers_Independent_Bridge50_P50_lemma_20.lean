-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P50.lemma_20
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:05:33.932464+00:00
-- url     : https://prove2.me/submissions/c220b8e5-0fb9-46ab-9470-1758dd28b9cf

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





open scoped Matrix MatrixOrder

lemma q20_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma q20_conj_eig {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix n n ℂ) * Y * (hY.eigenvectorUnitary : Matrix n n ℂ) =
      Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  have hu := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues) : Matrix n n ℂ) = D at *
  subst hs
  calc star U * (U * D * star U) * U
      = (star U * U) * D * (star U * U) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, one_mul, mul_one]

lemma q20_posPart_aux {n : Type*} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hU : U * star U = 1)
    (hD : star U * (A - B) * U = Matrix.diagonal (RCLike.ofReal ∘ lam)) :
    ∑ i, max (lam i) 0 ≤ A.trace.re := by
  have hA' := hA.conjTranspose_mul_mul_same U
  have hB' := hB.conjTranspose_mul_mul_same U
  have htr : A.trace = (Uᴴ * A * U).trace := by
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, hU, one_mul]
  rw [htr, Matrix.trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 : (Uᴴ * A * U) i i - (Uᴴ * B * U) i i = ((lam i : ℝ) : ℂ) := by
    have := congrArg (fun M => M i i) hD
    rw [Matrix.mul_sub, Matrix.sub_mul] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  have ha' : 0 ≤ ((Uᴴ * A * U) i i).re := (Complex.nonneg_iff.mp (hA'.diag_nonneg (i := i))).1
  have hb' : 0 ≤ ((Uᴴ * B * U) i i).re := (Complex.nonneg_iff.mp (hB'.diag_nonneg (i := i))).1
  have h2 := congrArg Complex.re h1
  simp only [Complex.sub_re, Complex.ofReal_re] at h2
  simp only [Matrix.diag]
  exact max_le (by linarith) ha'

lemma q20_parts {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma q20_cfc_psd {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma q20_posPart_le {n : Type*} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [q20_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := q20_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact q20_posPart_aux lam hA hB hu hD

lemma q20_negPart_eq {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]


lemma q20_td_le_one {I : Type*} [Fintype I] [DecidableEq I] {A B : Matrix I I ℂ}
    (hA : QAlgorithms.IsDensityMatrix A) (hB : QAlgorithms.IsDensityMatrix B) :
    QAlgorithms.traceDistance A B ≤ 1 := by
  have hY : (A - B).IsHermitian := hA.1.isHermitian.sub hB.1.isHermitian
  have h1 := q20_posPart_le hY hA.1 hB.1 rfl
  have h2 := q20_posPart_le hY.neg hB.1 hA.1 (by abel)
  rw [← q20_negPart_eq] at h2
  have htn : QAlgorithms.traceNorm (A - B) =
      (cfc (fun t : ℝ => max t 0) (A - B)).trace.re + (cfc (fun t : ℝ => max (-t) 0) (A - B)).trace.re := by
    have hsa : IsSelfAdjoint (A - B) := hY.isSelfAdjoint
    unfold QAlgorithms.traceNorm
    rw [hY.eq]
    have e1 : (A - B) * (A - B) = cfc (fun t : ℝ => t * t) (A - B) := by
      rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) (A - B), cfc_id' ℝ (A - B)]
    rw [e1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) (A - B), ← Complex.add_re, ← Matrix.trace_add,
      ← cfc_add (A - B) (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
    congr 2
    apply cfc_congr
    intro t _
    simp only [Function.comp]
    rw [← sq, Real.sqrt_sq_eq_abs]
    rcases le_total t 0 with h | h
    · rw [abs_of_nonpos h]; simp [h]
    · rw [abs_of_nonneg h]; simp [h]
  unfold QAlgorithms.traceDistance
  rw [htn]
  rw [hA.2] at h1; rw [hB.2] at h2
  simp at h1 h2
  linarith

lemma q20_td_nonneg {I : Type*} [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ) :
    0 ≤ QAlgorithms.traceDistance A B := by
  unfold QAlgorithms.traceDistance QAlgorithms.traceNorm
  have h := (q20_cfc_psd ((A - B)ᴴ * (A - B)) Real.sqrt Real.sqrt_nonneg).trace_nonneg
  have := (Complex.nonneg_iff.mp h).1
  positivity

theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) (n : ℕ) (hn : 1 ≤ n)
    (rho : Fin n → Mat I) (hrho : ∀ i, rho i ∈ S)
    (nu : ℝ) (hnu : 0 < nu ∧ nu < 1) (hbad : ¬ OmegaOne S nu rho) :
    ∃ Xi : Finset (Fin n), (n : ℝ) * nu / 2 < Xi.card ∧
      ∀ i ∈ Xi, nu/2 < peripheralDistance S (rho i) := by
  obtain ⟨hnu0, hnu1⟩ := hnu
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold OmegaOne at hbad
  push Not at hbad
  have hsum : (n : ℝ) * nu < ∑ i, peripheralDistance S (rho i) := by
    rw [inv_mul_eq_div, lt_div_iff₀ hnpos] at hbad; linarith
  have hnn : ∀ i, 0 ≤ peripheralDistance S (rho i) := by
    intro i
    apply Real.sInf_nonneg
    rintro r ⟨tau, -, rfl⟩
    exact q20_td_nonneg _ _
  have hne : (peripheralStates S).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : ∀ i, peripheralDistance S (rho i) = 0 := by
      intro i
      unfold peripheralDistance
      rw [h]; simp
    simp [this] at hsum
    nlinarith
  obtain ⟨tau, htau⟩ := hne
  have htauS : tau ∈ S := htau.1
  have hle : ∀ i, peripheralDistance S (rho i) ≤ 1 := by
    intro i
    unfold peripheralDistance
    refine le_trans (csInf_le ⟨0, ?_⟩ ⟨tau, htau, rfl⟩) ?_
    · rintro r ⟨t, -, rfl⟩; exact q20_td_nonneg _ _
    · exact q20_td_le_one (hS.2.2 _ (hrho i)) (hS.2.2 _ htauS)
  set d := fun i => peripheralDistance S (rho i) with hd
  refine ⟨Finset.univ.filter (fun i => nu / 2 < d i), ?_, ?_⟩
  · set X := Finset.univ.filter (fun i => nu / 2 < d i)
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => nu / 2 < d i) d
    have hA : ∑ i ∈ X, d i ≤ X.card := by
      have := Finset.sum_le_sum (s := X) (fun i _ => hle i)
      simpa using this
    have hB : ∑ i ∈ Finset.univ.filter (fun i => ¬ nu / 2 < d i), d i ≤
        (Finset.univ.filter (fun i => ¬ nu / 2 < d i)).card * (nu / 2) := by
      have := Finset.sum_le_sum (s := Finset.univ.filter (fun i => ¬ nu / 2 < d i))
        (f := d) (g := fun _ => nu / 2) (fun i hi => le_of_not_gt (Finset.mem_filter.mp hi).2)
      simpa using this
    have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => nu / 2 < d i)
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    have hcard' : (X.card : ℝ) + (Finset.univ.filter (fun i => ¬ nu / 2 < d i)).card = n := by
      exact_mod_cast hcard
    have hXle : (X.card : ℝ) ≤ n := by linarith [(Nat.cast_nonneg (α := ℝ) (Finset.univ.filter (fun i => ¬ nu / 2 < d i)).card)]
    have hs : (n : ℝ) * nu < X.card + (n - X.card) * (nu / 2) := by
      have : ∑ i, d i = ∑ i, peripheralDistance S (rho i) := rfl
      rw [← hcard'] at hsum ⊢
      nlinarith
    nlinarith
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
