-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.trace_coherence_axioms
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:41:19.055054+00:00
-- url     : https://prove2.me/submissions/87e17b33-b702-4dcd-bde2-f27992b211ab

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P04

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma s199t_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma s199t_conj_eig {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
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

lemma s199t_posPart_aux {n : Type} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
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

lemma s199t_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma s199t_cfc_psd {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma s199t_posPart_le {n : Type} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [s199t_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := s199t_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact s199t_posPart_aux lam hA hB hu hD

lemma s199t_traceNorm_herm {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.traceNorm X =
      (cfc (fun t : ℝ => max t 0) X).trace.re + (cfc (fun t : ℝ => max (-t) 0) X).trace.re := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  unfold QAlgorithms.traceNorm
  rw [hX.eq]
  have h1 : X * X = cfc (fun t : ℝ => t * t) X := by
    rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) X, cfc_id' ℝ X]
  rw [h1, ← cfc_comp Real.sqrt (fun t : ℝ => t * t) X, ← Complex.add_re, ← Matrix.trace_add,
    ← cfc_add X (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0)]
  congr 2
  apply cfc_congr
  intro t _
  simp only [Function.comp]
  rw [← sq, Real.sqrt_sq_eq_abs]
  rcases le_total t 0 with h | h
  · rw [abs_of_nonpos h]; simp [h]
  · rw [abs_of_nonneg h]; simp [h]

lemma s199t_negPart_eq {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]


lemma s199t_tn_le_sub {n : Type} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ}
    (hY : Y.IsHermitian) (hA : A.PosSemidef) (hB : B.PosSemidef) (h : Y = A - B) :
    QAlgorithms.traceNorm Y ≤ A.trace.re + B.trace.re := by
  rw [s199t_traceNorm_herm hY]
  have h1 := s199t_posPart_le hY hA hB h
  have h2 := s199t_posPart_le hY.neg hB hA (by rw [h]; abel)
  rw [← s199t_negPart_eq] at h2
  linarith

lemma s199t_re_tr_nonneg {n : Type} [Fintype n] {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    0 ≤ A.trace.re := (Complex.nonneg_iff.1 hA.trace_nonneg).1

lemma s199t_tn_nonneg {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) : 0 ≤ QAlgorithms.traceNorm X := by
  rw [s199t_traceNorm_herm hX]
  have := s199t_re_tr_nonneg (s199t_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _))
  have := s199t_re_tr_nonneg (s199t_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _))
  linarith

lemma s199t_psd_zero {n : Type} [Fintype n] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (h : A.trace.re = 0) : A = 0 := by
  rw [← hA.trace_eq_zero_iff]
  have := (Complex.nonneg_iff.1 hA.trace_nonneg).2
  apply Complex.ext <;> simp_all

lemma s199t_tn_eq_zero {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (h : QAlgorithms.traceNorm X = 0) : X = 0 := by
  rw [s199t_traceNorm_herm hX] at h
  have hP := s199t_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have hN := s199t_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have a := s199t_re_tr_nonneg hP
  have b := s199t_re_tr_nonneg hN
  rw [← s199t_parts X hX, s199t_psd_zero hP (by linarith), s199t_psd_zero hN (by linarith), sub_zero]

lemma s199t_tn_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ)
    (hX : X.IsHermitian) : ∃ P N : Matrix n n ℂ, P.PosSemidef ∧ N.PosSemidef ∧ X = P - N ∧
      QAlgorithms.traceNorm X = P.trace.re + N.trace.re :=
  ⟨_, _, s199t_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _),
    s199t_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _),
    (s199t_parts X hX).symm, s199t_traceNorm_herm hX⟩

lemma s199t_tn_add {n : Type} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    QAlgorithms.traceNorm (X + Y) ≤ QAlgorithms.traceNorm X + QAlgorithms.traceNorm Y := by
  obtain ⟨P, N, hP, hN, e, t⟩ := s199t_tn_parts X hX
  obtain ⟨P', N', hP', hN', e', t'⟩ := s199t_tn_parts Y hY
  have := s199t_tn_le_sub (hX.add hY) (hP.add hP') (hN.add hN') (by rw [e, e']; abel)
  rw [t, t']
  simp only [Matrix.trace_add, Complex.add_re] at this
  linarith

lemma s199t_tn_diag {n : Type} [Fintype n] [DecidableEq n] (q : n → ℝ) :
    QAlgorithms.traceNorm (Matrix.diagonal (fun i => (q i : ℂ))) ≤ ∑ i, |q i| := by
  have hA : (Matrix.diagonal (fun i => ((max (q i) 0 : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i
    exact_mod_cast le_max_right _ _
  have hB : (Matrix.diagonal (fun i => ((max (-q i) 0 : ℝ) : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i
    exact_mod_cast le_max_right _ _
  have hY : (Matrix.diagonal (fun i => (q i : ℂ))).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]; intro i; exact Complex.conj_ofReal _
  have := s199t_tn_le_sub hY hA hB (by
    rw [Matrix.diagonal_sub]; congr 1; funext i
    rcases le_total (q i) 0 with h | h <;> simp [h])
  refine this.trans (le_of_eq ?_)
  simp only [Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases le_total (q i) 0 with h | h
  · simp [h, abs_of_nonpos h]
  · simp [h, abs_of_nonneg h]

lemma s199t_dens_herm {d : ℕ} {rho sigma : CoherenceMatrix d} (h1 : IsDensityMatrix rho)
    (h2 : IsDensityMatrix sigma) : (rho - sigma).IsHermitian := h1.1.1.sub h2.1.1

lemma s199t_inc_diag {d : ℕ} {sigma : CoherenceMatrix d} (h : IncoherentState sigma) :
    sigma = Matrix.diagonal (fun i => (((sigma i i).re : ℝ) : ℂ)) ∧
      (fun i => (sigma i i).re) ∈ stdSimplex ℝ (Fin d) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    by_cases hij : i = j
    · subst hij
      have := congrFun h.1.1.1.coe_re_diag i
      simpa [Matrix.diagonal_apply] using this.symm
    · simp [Matrix.diagonal_apply, hij, h.2 i j hij]
  · intro i; exact (Complex.nonneg_iff.1 (h.1.1.diag_nonneg (i := i))).1
  · have := congrArg Complex.re h.1.2
    simpa [Matrix.trace, Complex.re_sum] using this

lemma s199t_simplex_inc {d : ℕ} {p : Fin d → ℝ} (hp : p ∈ stdSimplex ℝ (Fin d)) :
    IncoherentState (Matrix.diagonal (fun i => (p i : ℂ))) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.posSemidef_diagonal_iff]; intro i; exact_mod_cast hp.1 i
  · rw [Matrix.trace_diagonal]; exact_mod_cast hp.2
  · intro i j hij; simp [Matrix.diagonal_apply, hij]

lemma s199t_lip {d : ℕ} (rho : CoherenceMatrix d) (hrho : rho.IsHermitian) :
    Continuous (fun p : Fin d → ℝ =>
      QAlgorithms.traceNorm (rho - Matrix.diagonal (fun i => (p i : ℂ)))) := by
  have hH : ∀ p : Fin d → ℝ, (rho - Matrix.diagonal (fun i => (p i : ℂ))).IsHermitian := by
    intro p
    refine hrho.sub ?_
    rw [Matrix.isHermitian_diagonal_iff]; intro i; exact Complex.conj_ofReal _
  have hD : ∀ p : Fin d → ℝ, (Matrix.diagonal (fun i => (p i : ℂ))).IsHermitian := by
    intro p; rw [Matrix.isHermitian_diagonal_iff]; intro i; exact Complex.conj_ofReal _
  have key : ∀ p q : Fin d → ℝ,
      QAlgorithms.traceNorm (rho - Matrix.diagonal (fun i => (p i : ℂ))) ≤
        QAlgorithms.traceNorm (rho - Matrix.diagonal (fun i => (q i : ℂ))) + d * dist p q := by
    intro p q
    have e : rho - Matrix.diagonal (fun i => (p i : ℂ)) =
        (rho - Matrix.diagonal (fun i => (q i : ℂ))) +
          Matrix.diagonal (fun i => ((q i - p i : ℝ) : ℂ)) := by
      ext i j; by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.diagonal_apply, hij]
    rw [e]
    refine (s199t_tn_add (hH q) (hD _)).trans (add_le_add le_rfl ?_)
    refine (s199t_tn_diag _).trans ?_
    have : ∀ i, |q i - p i| ≤ dist p q := fun i => by
      rw [← Real.dist_eq, dist_comm]; exact dist_le_pi_dist p q i
    calc ∑ i, |q i - p i| ≤ ∑ _i : Fin d, dist p q := Finset.sum_le_sum fun i _ => this i
      _ = d * dist p q := by simp
  refine (LipschitzWith.of_dist_le_mul (K := (d : NNReal)) fun p q => ?_).continuous
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1 := key p q
  have h2 := key q p
  rw [dist_comm] at h2
  push_cast
  constructor <;> linarith

lemma s199t_attain {d : ℕ} (hd : 0 < d) (rho : CoherenceMatrix d) (hrho : IsDensityMatrix rho) :
    ∃ delta, IncoherentState delta ∧ ∀ sigma, IncoherentState sigma →
      fullTraceDistance d rho delta ≤ fullTraceDistance d rho sigma := by
  obtain ⟨p, hp, hmin⟩ := (isCompact_stdSimplex ℝ (Fin d)).exists_isMinOn
    ⟨_, single_mem_stdSimplex ℝ ⟨0, hd⟩⟩ (s199t_lip rho hrho.1.1).continuousOn
  refine ⟨_, s199t_simplex_inc hp, fun sigma hs => ?_⟩
  obtain ⟨e, hs'⟩ := s199t_inc_diag hs
  have := hmin hs'
  simp only [Set.mem_ofPred_eq] at this
  unfold fullTraceDistance
  conv_rhs => rw [e]
  exact this

lemma s199t_cand_eq {d : ℕ} (rho delta : CoherenceMatrix d) (hdelta : IncoherentState delta)
    (hmin : ∀ sigma, IncoherentState sigma →
      fullTraceDistance d rho delta ≤ fullTraceDistance d rho sigma) :
    distanceCandidate (fullTraceDistance d) rho = fullTraceDistance d rho delta := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨fullTraceDistance d rho delta, ?_⟩
      rintro v ⟨s, hs, rfl⟩
      exact hmin s hs
    · exact ⟨_, hdelta, rfl⟩
  · refine le_csInf ⟨_, delta, hdelta, rfl⟩ ?_
    rintro v ⟨s, hs, rfl⟩
    exact hmin s hs

lemma s199t_cand_le {d : ℕ} (rho delta : CoherenceMatrix d) (hrho : IsDensityMatrix rho)
    (hdelta : IncoherentState delta) :
    distanceCandidate (fullTraceDistance d) rho ≤ fullTraceDistance d rho delta := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨s, hs, rfl⟩
    exact s199t_tn_nonneg (s199t_dens_herm hrho hs.1)
  · exact ⟨_, hdelta, rfl⟩

lemma s199t_kraus_psd {a d e : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) : (krausApply K X).PosSemidef := by
  unfold krausApply
  exact Matrix.posSemidef_sum _ (fun i _ => hX.mul_mul_conjTranspose_same (K i))

lemma s199t_kraus_tr {a d e : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (X : Matrix (Fin d) (Fin d) ℂ) :
    (krausApply K X).trace = X.trace := by
  unfold krausApply
  rw [Matrix.trace_sum]
  have : ∀ i, (K i * X * (K i)ᴴ).trace = ((K i)ᴴ * K i * X).trace := by
    intro i; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

lemma s199t_kraus_sub {a d e : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    (X Y : Matrix (Fin d) (Fin d) ℂ) : krausApply K (X - Y) = krausApply K X - krausApply K Y := by
  unfold krausApply
  simp [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

lemma s199t_contract {a d e : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
    QAlgorithms.traceNorm (krausApply K X) ≤ QAlgorithms.traceNorm X := by
  obtain ⟨P, N, hP, hN, e, t⟩ := s199t_tn_parts X hX
  have hKX : krausApply K X = krausApply K P - krausApply K N := by rw [e, s199t_kraus_sub]
  have hH : (krausApply K X).IsHermitian := by
    rw [hKX]; exact (s199t_kraus_psd K hP).1.sub (s199t_kraus_psd K hN).1
  have := s199t_tn_le_sub hH (s199t_kraus_psd K hP) (s199t_kraus_psd K hN) hKX
  rw [s199t_kraus_tr K hK, s199t_kraus_tr K hK] at this
  rw [t]; exact this

lemma s199t_kraus_inc {a d e : ℕ} (K : Fin a → Matrix (Fin e) (Fin d) ℂ)
    (hK : IncoherentInstrument (fun _ => e) K) {delta : CoherenceMatrix d}
    (h : IncoherentState delta) : IncoherentState (krausApply K delta) := by
  refine ⟨⟨s199t_kraus_psd K h.1.1, ?_⟩, ?_⟩
  · rw [s199t_kraus_tr K hK.1]; exact h.1.2
  · intro i j hij
    unfold krausApply
    rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero (fun k _ => hK.2 k delta h.1.1 h.2 i j hij)

lemma s199t_mix_density {d a : ℕ} (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d)
    (hp : Learning.IsDistribution p) (hr : ∀ i, IsDensityMatrix (rho i)) :
    IsDensityMatrix (ensembleMixture p rho) := by
  refine ⟨?_, ?_⟩
  · unfold ensembleMixture
    exact Matrix.posSemidef_sum _ (fun i _ =>
      (hr i).1.smul (by exact_mod_cast hp.1 i))
  · unfold ensembleMixture
    rw [Matrix.trace_sum]
    simp_rw [Matrix.trace_smul, (hr _).2, smul_eq_mul, mul_one]
    exact_mod_cast hp.2

lemma s199t_mix_inc {d a : ℕ} (p : Fin a → ℝ) (rho : Fin a → CoherenceMatrix d)
    (hp : Learning.IsDistribution p) (hr : ∀ i, IncoherentState (rho i)) :
    IncoherentState (ensembleMixture p rho) := by
  refine ⟨s199t_mix_density p rho hp (fun i => (hr i).1), ?_⟩
  intro i j hij
  unfold ensembleMixture
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero (fun k _ => by simp [(hr k).2 i j hij])

lemma s199t_joint {d a : ℕ} (p : Fin a → ℝ) (rho sigma : Fin a → CoherenceMatrix d)
    (hp : Learning.IsDistribution p) (hr : ∀ i, IsDensityMatrix (rho i))
    (hs : ∀ i, IsDensityMatrix (sigma i)) :
    QAlgorithms.traceNorm (ensembleMixture p rho - ensembleMixture p sigma) ≤
      ∑ i, p i * QAlgorithms.traceNorm (rho i - sigma i) := by
  have := fun i => s199t_tn_parts (rho i - sigma i) (s199t_dens_herm (hr i) (hs i))
  choose P N hP hN e t using this
  have hPs : (∑ i, (p i : ℂ) • P i).PosSemidef :=
    Matrix.posSemidef_sum _ (fun i _ => (hP i).smul (by exact_mod_cast hp.1 i))
  have hNs : (∑ i, (p i : ℂ) • N i).PosSemidef :=
    Matrix.posSemidef_sum _ (fun i _ => (hN i).smul (by exact_mod_cast hp.1 i))
  have hE : ensembleMixture p rho - ensembleMixture p sigma =
      ∑ i, (p i : ℂ) • P i - ∑ i, (p i : ℂ) • N i := by
    unfold ensembleMixture
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_sub, ← smul_sub, ← e i]
  have hH := s199t_dens_herm (s199t_mix_density p rho hp hr) (s199t_mix_density p sigma hp hs)
  refine (s199t_tn_le_sub hH hPs hNs hE).trans (le_of_eq ?_)
  simp only [Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul,
    t, mul_add, Finset.sum_add_distrib]

theorem solution :
    DistanceAttainment fullTraceDistance ∧
    CoherenceNonnegative (fun d => distanceCandidate (fullTraceDistance d)) ∧
    CoherenceFaithful (fun d => distanceCandidate (fullTraceDistance d)) ∧
    CoherenceMonotone (fun d => distanceCandidate (fullTraceDistance d)) ∧
    CoherenceConvex (fun d => distanceCandidate (fullTraceDistance d)) := by
  refine ⟨fun d hd rho hrho => s199t_attain hd rho hrho, ?_, ?_, ?_, ?_⟩
  · intro d hd rho hrho
    obtain ⟨delta, hdelta, hmin⟩ := s199t_attain hd rho hrho
    show 0 ≤ distanceCandidate (fullTraceDistance d) rho
    rw [s199t_cand_eq rho delta hdelta hmin]
    exact s199t_tn_nonneg (s199t_dens_herm hrho hdelta.1)
  · intro d hd rho hrho
    obtain ⟨delta, hdelta, hmin⟩ := s199t_attain hd rho hrho
    show distanceCandidate (fullTraceDistance d) rho = 0 ↔ _
    rw [s199t_cand_eq rho delta hdelta hmin]
    constructor
    · intro h
      have := s199t_tn_eq_zero (s199t_dens_herm hrho hdelta.1) h
      rw [sub_eq_zero.1 this]; exact hdelta
    · intro h
      apply le_antisymm
      · have := hmin rho h
        have h0 : QAlgorithms.traceNorm (0 : CoherenceMatrix d) ≤ 0 := by
          simpa using s199t_tn_le_sub (Y := (0 : CoherenceMatrix d)) Matrix.isHermitian_zero
            Matrix.PosSemidef.zero Matrix.PosSemidef.zero (sub_zero 0).symm
        simp only [fullTraceDistance, sub_self] at this
        exact this.trans h0
      · exact s199t_tn_nonneg (s199t_dens_herm hrho hdelta.1)
  · intro d e hd he a K hK rho hrho
    obtain ⟨delta, hdelta, hmin⟩ := s199t_attain hd rho hrho
    have hKr : IsDensityMatrix (krausApply K rho) :=
      ⟨s199t_kraus_psd K hrho.1, by rw [s199t_kraus_tr K hK.1]; exact hrho.2⟩
    have h1 := s199t_cand_le (krausApply K rho) _ hKr (s199t_kraus_inc K hK hdelta)
    have h2 := s199t_cand_eq rho delta hdelta hmin
    have h3 : fullTraceDistance e (krausApply K rho) (krausApply K delta) ≤
        fullTraceDistance d rho delta := by
      unfold fullTraceDistance
      rw [← s199t_kraus_sub]
      exact s199t_contract K hK.1 _ (s199t_dens_herm hrho hdelta.1)
    show distanceCandidate (fullTraceDistance e) (krausApply K rho) ≤
      distanceCandidate (fullTraceDistance d) rho
    linarith
  · intro d hd a p rho hp hr
    have := fun i => s199t_attain hd (rho i) (hr i)
    choose sigma hs hmin using this
    have heq : ∀ i, distanceCandidate (fullTraceDistance d) (rho i) =
        fullTraceDistance d (rho i) (sigma i) :=
      fun i => s199t_cand_eq _ _ (hs i) (hmin i)
    have h1 := s199t_cand_le _ _ (s199t_mix_density p rho hp hr) (s199t_mix_inc p sigma hp hs)
    have h2 := s199t_joint p rho sigma hp hr (fun i => (hs i).1)
    show distanceCandidate (fullTraceDistance d) (ensembleMixture p rho) ≤
      ∑ i, p i * distanceCandidate (fullTraceDistance d) (rho i)
    simp_rw [heq]
    exact h1.trans h2

