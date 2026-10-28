-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P22.collectiveMixture
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T07:42:34.584987+00:00
-- url     : https://prove2.me/submissions/f5d2a00e-7075-4f4a-a0ec-f4a2babd0d32

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P22
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Support50.P22

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P18 (ClassicalOutput)

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixBorelSpace

open QAlgorithms
open scoped MatrixOrder

lemma p22_tn_cont {ι : Type} [Fintype ι] [DecidableEq ι] :
    Continuous (fun M : Matrix ι ι ℂ => QAlgorithms.traceNorm M) := by
  unfold QAlgorithms.traceNorm
  have h : Continuous (fun M : Matrix ι ι ℂ => cfc Real.sqrt (Mᴴ * M)) := by
    refine Continuous.cfc_of_mem_nhdsSet (s := Set.univ) Real.sqrt (by simp) (by fun_prop)
      (fun M => ?_) Real.continuous_sqrt.continuousOn
    exact (Matrix.isHermitian_conjTranspose_mul_self M).isSelfAdjoint
  exact Complex.continuous_re.comp ((Continuous.matrix_trace) h)

lemma p22_tn_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    0 ≤ QAlgorithms.traceNorm M := by
  unfold QAlgorithms.traceNorm
  have hp : (cfc Real.sqrt (Mᴴ * M)).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact cfc_nonneg (A := Matrix ι ι ℂ) (fun t _ => Real.sqrt_nonneg t)
  exact (Complex.nonneg_iff.mp hp.trace_nonneg).1

lemma p22_tn_smul {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) {c : ℝ} (hc : 0 ≤ c) :
    QAlgorithms.traceNorm (c • M) = c * QAlgorithms.traceNorm M := by
  unfold QAlgorithms.traceNorm
  have h1 : (c • M)ᴴ * (c • M) = (c ^ 2) • (Mᴴ * M) := by
    rw [Matrix.conjTranspose_smul, star_trivial, smul_mul_smul_comm, sq]
  rw [h1]
  have hsa : IsSelfAdjoint (Mᴴ * M) := (Matrix.isHermitian_conjTranspose_mul_self M).isSelfAdjoint
  rw [← cfc_comp_smul (c ^ 2) Real.sqrt (Mᴴ * M)]
  have h2 : cfc (fun x => Real.sqrt (c ^ 2 • x)) (Mᴴ * M) = cfc (fun x => c * Real.sqrt x) (Mᴴ * M) := by
    apply cfc_congr
    intro x _
    simp only [smul_eq_mul]
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rw [h2, cfc_const_mul c Real.sqrt (Mᴴ * M), Matrix.trace_smul]
  simp
lemma p22_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma p22_conj_eig {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
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

lemma p22_posPart_aux {n : Type} [Fintype n] [DecidableEq n] {A B U : Matrix n n ℂ} (lam : n → ℝ)
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

lemma p22_parts {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    cfc (fun t : ℝ => max t 0) X - cfc (fun t : ℝ => max (-t) 0) X = X := by
  have hsa : IsSelfAdjoint X := hX.isSelfAdjoint
  rw [← cfc_sub (fun t : ℝ => max t 0) (fun t : ℝ => max (-t) 0) X]
  conv_rhs => rw [← cfc_id ℝ X]
  apply cfc_congr
  intro t _
  simp only [id]
  rcases le_total t 0 with h | h <;> simp [h]

lemma p22_cfc_psd {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t) : (cfc f X).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => hf t)

lemma p22_posPart_le {n : Type} [Fintype n] [DecidableEq n] {Y A B : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hYAB : Y = A - B) :
    (cfc (fun t : ℝ => max t 0) Y).trace.re ≤ A.trace.re := by
  rw [p22_cfc_trace hY, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hD := p22_conj_eig hY
  have hu := Unitary.mul_star_self_of_mem hY.eigenvectorUnitary.2
  generalize (hY.eigenvectorUnitary : Matrix n n ℂ) = U at *
  generalize hY.eigenvalues = lam at *
  subst hYAB
  exact p22_posPart_aux lam hA hB hu hD

lemma p22_traceNorm_herm {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
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

lemma p22_negPart_eq {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    cfc (fun t : ℝ => max (-t) 0) X = cfc (fun t : ℝ => max t 0) (-X) := by
  by_cases hX : IsSelfAdjoint X
  · exact cfc_comp_neg (f := fun t : ℝ => max t 0) (a := X)
  · have : ¬ IsSelfAdjoint (-X) := fun h => hX (by simpa using h.neg)
    rw [cfc_apply_of_not_predicate X hX, cfc_apply_of_not_predicate (-X) this]

/-- trace-norm triangle inequality for Hermitian matrices -/
lemma p22_traceNorm_add_le {n : Type} [Fintype n] [DecidableEq n] {X Y : Matrix n n ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    QAlgorithms.traceNorm (X + Y) ≤ QAlgorithms.traceNorm X + QAlgorithms.traceNorm Y := by
  have hXY : (X + Y).IsHermitian := hX.add hY
  rw [p22_traceNorm_herm hXY, p22_traceNorm_herm hX, p22_traceNorm_herm hY]
  have pX := p22_cfc_psd X (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mX := p22_cfc_psd X (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have pY := p22_cfc_psd Y (fun t : ℝ => max t 0) (fun t => le_max_right _ _)
  have mY := p22_cfc_psd Y (fun t : ℝ => max (-t) 0) (fun t => le_max_right _ _)
  have eX := p22_parts X hX
  have eY := p22_parts Y hY
  have e1 : X + Y = (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) -
      (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) := by
    conv_lhs => rw [← eX, ← eY]
    abel
  have e2 : -(X + Y) = (cfc (fun t : ℝ => max (-t) 0) X + cfc (fun t : ℝ => max (-t) 0) Y) -
      (cfc (fun t : ℝ => max t 0) X + cfc (fun t : ℝ => max t 0) Y) := by
    rw [e1]; abel
  have h1 := p22_posPart_le hXY (pX.add pY) (mX.add mY) e1
  have h2 := p22_posPart_le hXY.neg (mX.add mY) (pX.add pY) e2
  rw [← p22_negPart_eq] at h2
  rw [Matrix.trace_add, Complex.add_re] at h1 h2
  linarith

def p22T {A B R : Type*} [Fintype A] [Fintype B] [Fintype R]
    (D : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    Matrix (A × R) (A × R) ℂ →ₗ[ℂ] Matrix (B × R) (B × R) ℂ where
  toFun X := tensorId (⇑D) X
  map_add' X Y := by
    ext p q
    simp only [tensorId, idTensorSuperop, Matrix.of_apply, Matrix.add_apply]
    have : (Matrix.of fun i i' => X ((p.2, i).2, (p.2, i).1) ((q.2, i').2, (q.2, i').1) +
        Y ((p.2, i).2, (p.2, i).1) ((q.2, i').2, (q.2, i').1)) =
        (Matrix.of fun i i' => X ((p.2, i).2, (p.2, i).1) ((q.2, i').2, (q.2, i').1)) +
        (Matrix.of fun i i' => Y ((p.2, i).2, (p.2, i).1) ((q.2, i').2, (q.2, i').1)) := by
      ext; simp
    rw [this, map_add]; rfl
  map_smul' c X := by
    ext p q
    simp only [tensorId, idTensorSuperop, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    have : (Matrix.of fun i i' => c • X ((p.2, i).2, (p.2, i).1) ((q.2, i').2, (q.2, i').1)) =
        c • (Matrix.of fun i i' => X ((p.2, i).2, (p.2, i).1) ((q.2, i').2, (q.2, i').1)) := by
      ext; simp
    rw [this, map_smul]; rfl

lemma p22T_apply {A B R : Type*} [Fintype A] [Fintype B] [Fintype R]
    (D : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (X : Matrix (A × R) (A × R) ℂ) :
    p22T D X = tensorId (⇑D) X := rfl

lemma p22T_herm {A B R : Type*} [Fintype A] [Fintype B] [Fintype R]
    (D : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) (hD : ∀ Y, D Yᴴ = (D Y)ᴴ)
    {X : Matrix (A × R) (A × R) ℂ} (hX : X.IsHermitian) :
    (tensorId (⇑D) X).IsHermitian := by
  ext p q
  simp only [tensorId, idTensorSuperop, Matrix.of_apply, Matrix.conjTranspose_apply]
  have : (Matrix.of fun i i' => X ((p.2, i).2, (p.2, i).1) ((q.2, i').2, (q.2, i').1)) =
      (Matrix.of fun i i' => X ((q.2, i).2, (q.2, i).1) ((p.2, i').2, (p.2, i').1))ᴴ := by
    ext i i'
    simp only [Matrix.of_apply, Matrix.conjTranspose_apply]
    rw [← Matrix.conjTranspose_apply X, hX.eq]
  rw [this, hD, Matrix.conjTranspose_apply]

lemma p22_kraus_herm {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) (hE : IsChannel (⇑E)) (Y : Matrix ι ι ℂ) :
    E Yᴴ = (E Y)ᴴ := by
  obtain ⟨m, K, _, hK⟩ := hE
  rw [hK, hK]
  simp only [krausApply, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma p22_key_apply {L C : Type} [Fintype L] [Fintype C] (len : L → ℕ)
    (Y : Matrix (KeyOut L C len) (KeyOut L C len) ℂ) (a b : KeyOut L C len) :
    keyReplacement len Y a b = if a = b ∧ a.2.1.1 = a.2.1.2 then
    ((2 : ℂ) ^ len a.1)⁻¹ * ∑ s : Qubits (len a.1), ∑ t : Qubits (len a.1),
      Y ⟨a.1,((s,t),a.2.2)⟩ ⟨a.1,((s,t),a.2.2)⟩ else 0 := by
  change (∑ i, ∑ j, Y i j * replaceKeys len (Matrix.single i j 1) a b) = _
  simp only [replaceKeys]
  split_ifs with h
  · have key : ∀ x : KeyOut L C len, ∑ i, ∑ j, Y i j * Matrix.single i j (1 : ℂ) x x = Y x x := by
      intro x
      simp [Matrix.single_apply, ite_and]
    simp only [← key]
    simp only [Finset.mul_sum]
    conv_lhs => enter [2, i]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i, 2, s]; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => enter [2, s]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp

lemma p22_key_herm {L C : Type} [Fintype L] [Fintype C] (len : L → ℕ)
    (Y : Matrix (KeyOut L C len) (KeyOut L C len) ℂ) :
    keyReplacement len Yᴴ = (keyReplacement len Y)ᴴ := by
  ext a b
  rw [Matrix.conjTranspose_apply, p22_key_apply, p22_key_apply]
  by_cases h : a = b
  · subst h
    by_cases h2 : a.2.1.1 = a.2.1.2
    · simp only [h2, and_self, if_true, star_mul', star_sum, Matrix.conjTranspose_apply, star_inv₀, star_pow]
      simp
    · simp [h2]
  · simp [h, Ne.symm h]

lemma p22_D_herm {L C : Type} [Fintype L] [Fintype C] {ι : Type} [Fintype ι] [DecidableEq ι]
    (len : L → ℕ) (E : Matrix ι ι ℂ →ₗ[ℂ] Matrix (KeyOut L C len) (KeyOut L C len) ℂ)
    (hE : IsChannel (⇑E)) (Y : Matrix ι ι ℂ) :
    (E - idealProtocol len E) Yᴴ = ((E - idealProtocol len E) Y)ᴴ := by
  simp only [LinearMap.sub_apply, idealProtocol, LinearMap.comp_apply, Matrix.conjTranspose_sub,
    p22_kraus_herm E hE, p22_key_herm]

lemma p22_pairVector_norm (d : ℕ) (psi : EuclideanSpace ℂ (Fin (d*d))) :
    ‖pairVector d psi‖ = ‖psi‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp finProdFinEquiv (fun y => ‖psi y‖ ^ 2)

lemma p22_pd_herm {ι : Type} (φ : EuclideanSpace ℂ ι) : (pureDensity φ).IsHermitian := by
  ext a b
  simp [pureDensity, Matrix.conjTranspose_apply, mul_comm]

lemma p22_pp_herm (n d : ℕ) {ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (h : ρ.IsHermitian) :
    (pairedPower n d ρ).IsHermitian := by
  ext a b
  simp only [pairedPower, Matrix.conjTranspose_apply, star_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Matrix.conjTranspose_apply ρ, h.eq]

lemma p22_pp_cont (n d : ℕ) :
    Continuous (fun φ : EuclideanSpace ℂ (Fin d × Fin d) => pairedPower n d (pureDensity φ)) := by
  unfold pairedPower pureDensity
  refine continuous_pi fun a => continuous_pi fun b => ?_
  refine continuous_finsetProd _ fun i _ => ?_
  simp only [Matrix.of_apply]
  fun_prop

theorem solution (n d : ℕ) (hd : 0 < d)
    {L C : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (len : L → ℕ)
    (E : Matrix (Copies (Fin d) n) (Copies (Fin d) n) ℂ →ₗ[ℂ]
      Matrix (KeyOut L C len) (KeyOut L C len) ℂ)
    (hE : IsChannel E) (hclass : ClassicalOutput E)
    (epsilonBar : ℝ) (hepsilon : 0 ≤ epsilonBar)
    (hcollective : ∀ phi : EuclideanSpace ℂ (Fin d × Fin d), IsState phi →
      traceNorm (tensorId (E - idealProtocol len E)
        (pairedPower n d (pureDensity phi))) ≤ epsilonBar) :
    ∃ phiMax : EuclideanSpace ℂ (Fin d × Fin d), IsState phiMax ∧
      (∀ phi : EuclideanSpace ℂ (Fin d × Fin d), IsState phi →
        traceNorm (tensorId (E - idealProtocol len E) (pairedPower n d (pureDensity phi))) ≤
        traceNorm (tensorId (E - idealProtocol len E) (pairedPower n d (pureDensity phiMax)))) ∧
      traceNorm (tensorId (E - idealProtocol len E) (tauPair n d hd)) ≤
        traceNorm (tensorId (E - idealProtocol len E) (pairedPower n d (pureDensity phiMax))) ∧
      traceNorm (tensorId (E - idealProtocol len E) (pairedPower n d (pureDensity phiMax))) ≤
        epsilonBar := by
  set D := E - idealProtocol len E with hDdef
  have hD : ∀ Y, D Yᴴ = (D Y)ᴴ := p22_D_herm len E hE
  let T := p22T (R := Copies (Fin d) n) D
  have hTc : Continuous T := LinearMap.continuous_of_finiteDimensional T
  have hΦc : Continuous (fun φ : EuclideanSpace ℂ (Fin d × Fin d) =>
      traceNorm (tensorId (⇑D) (pairedPower n d (pureDensity φ)))) :=
    p22_tn_cont.comp (hTc.comp (p22_pp_cont n d))
  have : Nonempty (Fin d × Fin d) := ⟨(⟨0, hd⟩, ⟨0, hd⟩)⟩
  have hne : (Metric.sphere (0 : EuclideanSpace ℂ (Fin d × Fin d)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨φm, hφm, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ (Fin d × Fin d)) 1).exists_isMaxOn
    hne hΦc.continuousOn
  have hφm' : IsState φm := by simpa [IsState] using hφm
  have hall : ∀ φ : EuclideanSpace ℂ (Fin d × Fin d), IsState φ →
      traceNorm (tensorId (⇑D) (pairedPower n d (pureDensity φ))) ≤
      traceNorm (tensorId (⇑D) (pairedPower n d (pureDensity φm))) := by
    intro φ hφ
    exact hmax (by simpa [IsState] using hφ)
  refine ⟨φm, hφm', hall, ?_, hcollective φm hφm'⟩
  set M := traceNorm (tensorId (⇑D) (pairedPower n d (pureDensity φm))) with hM
  have hM0 : 0 ≤ M := p22_tn_nonneg _
  set μ := QAlgorithms.QuditFidelity.haarPureStateLaw (d*d) (Nat.mul_pos hd hd) with hμ
  have : IsProbabilityMeasure μ := ⟨QAlgorithms.QuditFidelity.haarPureStateLaw_univ _ _⟩
  let g := fun psi : EuclideanSpace ℂ (Fin (d*d)) => pairedPower n d (pureDensity (pairVector d psi))
  have htau : tauPair n d hd = ∫ psi, g psi ∂μ := rfl
  by_cases hint : Integrable g μ
  · let S : Set (Matrix (KeyOut L C len × Copies (Fin d) n) (KeyOut L C len × Copies (Fin d) n) ℂ) :=
      {X | X.IsHermitian ∧ traceNorm X ≤ M}
    have hconv : Convex ℝ S := by
      intro X hX Y hY a b ha hb hab
      have hXa : (a • X).IsHermitian := hX.1.smul (IsSelfAdjoint.all a)
      have hYb : (b • Y).IsHermitian := hY.1.smul (IsSelfAdjoint.all b)
      refine ⟨hXa.add hYb, ?_⟩
      calc traceNorm (a • X + b • Y) ≤ traceNorm (a • X) + traceNorm (b • Y) :=
            p22_traceNorm_add_le hXa hYb
        _ = a * traceNorm X + b * traceNorm Y := by rw [p22_tn_smul X ha, p22_tn_smul Y hb]
        _ ≤ a * M + b * M := by
            gcongr
            · exact hX.2
            · exact hY.2
        _ = M := by rw [← add_mul, hab, one_mul]
    have hclosed : IsClosed S := by
      have h1 : IsClosed {X : Matrix (KeyOut L C len × Copies (Fin d) n)
          (KeyOut L C len × Copies (Fin d) n) ℂ | Xᴴ = X} :=
        isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
      exact h1.inter (isClosed_le p22_tn_cont continuous_const)
    have hmeas : MeasurableSet {psi : EuclideanSpace ℂ (Fin (d*d)) | IsState psi} :=
      (isClosed_eq continuous_norm continuous_const).measurableSet
    have hst : ∀ᵐ psi ∂μ, IsState psi := by
      rw [hμ, QAlgorithms.QuditFidelity.haarPureStateLaw,
        ae_map_iff (QAlgorithms.QuditFidelity.haarState_continuous _ _).measurable.aemeasurable hmeas]
      exact Filter.Eventually.of_forall fun U => by
        rw [IsState, act_norm_of_mem_unitaryGroup U.property]; simp [ket]
    have hae : ∀ᵐ psi ∂μ, T (g psi) ∈ S := by
      filter_upwards [hst] with psi hpsi
      exact ⟨p22T_herm D hD (p22_pp_herm n d (p22_pd_herm _)),
        hall _ (by rw [IsState, p22_pairVector_norm]; exact hpsi)⟩
    have hmem := hconv.integral_mem hclosed hae
      ((LinearMap.toContinuousLinearMap T).integrable_comp hint)
    have hcomm : ∫ psi, T (g psi) ∂μ = T (∫ psi, g psi ∂μ) :=
      (LinearMap.toContinuousLinearMap T).integral_comp_comm hint
    rw [hcomm] at hmem
    rw [htau]
    exact hmem.2
  · rw [htau, integral_undef hint]
    have : tensorId (⇑D) (0 : Matrix (Copies (Fin d) n × Copies (Fin d) n)
        (Copies (Fin d) n × Copies (Fin d) n) ℂ) = 0 := map_zero T
    rw [this]
    simpa [QAlgorithms.traceNorm, cfc_zero] using hM0
