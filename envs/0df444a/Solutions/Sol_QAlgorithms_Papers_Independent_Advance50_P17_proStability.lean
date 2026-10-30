-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P17.proStability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:10:49.132913+00:00
-- url     : https://prove2.me/submissions/e55a8f37-f688-488b-a583-c8f85582b4e5

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17
noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P17

open scoped ComplexOrder MatrixOrder Kronecker

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

lemma qs5_choi_entry {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {ι : Type} [Fintype ι]
    (K : ι → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = ∑ j, K j * ρ * (K j)ᴴ)
    (p q : I × I) :
    normalizedProcessState E p q =
      (∑ j, K j p.2 p.1 * conj (K j q.2 q.1)) / (Fintype.card I : ℂ) := by
  simp only [normalizedProcessState, idTensorSuperop, Matrix.of_apply, hE,
    pureDensity, finiteMaxEntangled]
  rw [Matrix.sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  simp [apply_ite (starRingEnd ℂ), mul_ite, ite_mul, Finset.sum_ite_eq]
  have hd : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ^ 2 = (Fintype.card I : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have hd0 : ((Real.sqrt (Fintype.card I) : ℝ) : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  rw [← hd]
  field_simp

lemma qs5_trace {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (hK : IsKrausFamily K) (E : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).trace = 1 := by
  have hd0 : (Fintype.card I : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  simp only [Matrix.trace, Matrix.diag, qs5_choi_entry K E hE]
  rw [← Finset.sum_div, div_eq_one_iff_eq hd0, Fintype.sum_prod_type]
  have h1 : ∀ a : I, ∑ b : I, ∑ j, K j b a * conj (K j b a) = 1 := by
    intro a
    have := congrArg (fun M => M a a) hK
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq] at this
    rw [← this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
    simp [mul_comm]
  simp [h1]

lemma qs5_psd {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).PosSemidef := by
  have heq : normalizedProcessState E = (Fintype.card I : ℂ)⁻¹ •
      ∑ j, Matrix.vecMulVec (fun p : I × I => K j p.2 p.1) (star fun p : I × I => K j p.2 p.1) := by
    ext p q
    rw [qs5_choi_entry K E hE]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply, div_eq_inv_mul]
  rw [heq]
  refine Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ fun j _ =>
    Matrix.posSemidef_vecMulVec_self_star _) ?_
  exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)

lemma qs5_density {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E : Superop I I)
    (hE : IsChannel E) : IsDensityMatrix (normalizedProcessState E) := by
  obtain ⟨m, K, hK, hEK⟩ := hE
  exact ⟨qs5_psd K _ hEK, qs5_trace K hK _ hEK⟩

lemma qs5_of_kraus {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] {ι : Type} [Fintype ι]
    (K : ι → Matrix B A ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (E : Superop A B)
    (hE : ∀ ρ, E ρ = ∑ j, K j * ρ * (K j)ᴴ) : IsChannel E := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun t => K (e.symm t), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← hK]
    exact Equiv.sum_comp e.symm (fun j => (K j)ᴴ * K j)
  · intro ρ
    rw [hE]
    unfold krausApply
    exact (Equiv.sum_comp e.symm (fun j => K j * ρ * (K j)ᴴ)).symm

lemma qs5h_sqrt_unique {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hB : B.PosSemidef) (h : B * B = A) : cfc Real.sqrt A = B := by
  have hA : A.PosSemidef := by
    rw [← h]; have := Matrix.posSemidef_conjTranspose_mul_self B; rwa [hB.1.eq] at this
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_unique h hB.nonneg

lemma qs5h_sqrt_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    (cfc Real.sqrt A).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun x _ => Real.sqrt_nonneg x)

lemma qs5h_sqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt A hA.nonneg]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma qs5h_sqrt_kron {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    cfc Real.sqrt (A ⊗ₖ B) = cfc Real.sqrt A ⊗ₖ cfc Real.sqrt B := by
  apply qs5h_sqrt_unique ((qs5h_sqrt_psd A).kronecker (qs5h_sqrt_psd B))
  rw [← Matrix.mul_kronecker_mul, qs5h_sqrt_sq hA, qs5h_sqrt_sq hB]

lemma qs5h_M_psd {k : Type*} [Fintype k] [DecidableEq k] (X Y : Matrix k k ℂ) (hY : Y.PosSemidef) :
    (cfc Real.sqrt X * Y * cfc Real.sqrt X).PosSemidef := by
  have := hY.conjTranspose_mul_mul_same (cfc Real.sqrt X)
  rwa [(qs5h_sqrt_psd X).1.eq] at this

lemma qs5h_rootFid_kron {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A C : Matrix m m ℂ} {B D : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hC : C.PosSemidef) (hD : D.PosSemidef) :
    QAlgorithms.rootFidelity (Matrix.kronecker A B) (Matrix.kronecker C D) =
      QAlgorithms.rootFidelity A C * QAlgorithms.rootFidelity B D := by
  show QAlgorithms.rootFidelity (A ⊗ₖ B) (C ⊗ₖ D) = _
  unfold QAlgorithms.rootFidelity
  rw [qs5h_sqrt_kron hA hB, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    qs5h_sqrt_kron (qs5h_M_psd A C hC) (qs5h_M_psd B D hD), Matrix.trace_kronecker]
  have h1 := (qs5h_sqrt_psd (cfc Real.sqrt A * C * cfc Real.sqrt A)).trace_nonneg
  have h2 := (qs5h_sqrt_psd (cfc Real.sqrt B * D * cfc Real.sqrt B)).trace_nonneg
  rw [Complex.mul_re, (Complex.nonneg_iff.1 h1).2.symm, (Complex.nonneg_iff.1 h2).2.symm]
  ring


lemma qs5_idT_kraus {R I : Type} [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I] {m : ℕ}
    (A : Fin m → Matrix I I ℂ) (E : Superop I I) (hEA : ∀ ρ, E ρ = krausApply A ρ) :
    ∀ ρ, idTensorSuperop (R := R) E ρ =
      ∑ j, ((1 : Matrix R R ℂ) ⊗ₖ A j) * ρ * ((1 : Matrix R R ℂ) ⊗ₖ A j)ᴴ := by
  intro ρ
  ext p q
  simp only [idTensorSuperop, Matrix.of_apply, hEA, krausApply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  conv_rhs => rw [Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp [Finset.sum_mul]

lemma qs5_idT_channel {R I : Type} [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]
    (E : Superop I I) (hE : IsChannel E) : IsChannel (idTensorSuperop (R := R) E) := by
  obtain ⟨m, A, hA, hEA⟩ := hE
  refine qs5_of_kraus (ι := Fin m) _ ?_ _ (qs5_idT_kraus A E hEA)
  unfold IsKrausFamily at hA
  simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.mul_one]
  have : ∑ j, (1 : Matrix R R ℂ) ⊗ₖ ((A j)ᴴ * A j) = (1 : Matrix R R ℂ) ⊗ₖ (∑ j, (A j)ᴴ * A j) := by
    ext p q; simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]
  rw [this, hA, Matrix.one_kronecker_one]

/-- reference state = Choi state of identity -/
def qs5tau (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] : Matrix (J × J) (J × J) ℂ :=
  normalizedProcessState (id : Superop J J)

lemma qs5tau_id (J : Type) [Fintype J] [DecidableEq J] :
    ∀ ρ : Matrix J J ℂ, (id : Superop J J) ρ = ∑ _j : Unit, (1 : Matrix J J ℂ) * ρ * (1 : Matrix J J ℂ)ᴴ := by
  intro ρ; simp

lemma qs5tau_entry (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] (p q : J × J) :
    qs5tau J p q = ((1 : Matrix J J ℂ) p.2 p.1 * conj ((1 : Matrix J J ℂ) q.2 q.1)) / (Fintype.card J : ℂ) := by
  unfold qs5tau
  rw [qs5_choi_entry _ _ (qs5tau_id J)]
  simp

lemma qs5tau_density (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] :
    IsDensityMatrix (qs5tau J) :=
  qs5_density _ ⟨1, fun _ => 1, by simp [IsKrausFamily], fun ρ => by simp [krausApply]⟩

lemma qs5tau_idem (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] :
    qs5tau J * qs5tau J = qs5tau J := by
  have hd0 : (Fintype.card J : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  ext p q
  simp only [Matrix.mul_apply, qs5tau_entry, Fintype.sum_prod_type, Matrix.one_apply]
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, mul_ite, ite_mul, mul_one, one_mul,
    mul_zero, zero_mul, zero_div]
  have hx : ∀ x x1 : J, (if x1 = x then (1:ℂ) else 0) ^ 2 / (Fintype.card J : ℂ) ^ 2 =
      if x1 = x then 1 / (Fintype.card J : ℂ) ^ 2 else 0 := by
    intro x x1; split_ifs <;> simp
  by_cases h1 : p2 = p1 <;> by_cases h2 : q2 = q1 <;> simp [h1, h2]
  have hs : ∀ x : J, ∑ x1 : J, (if x1 = x then (1:ℂ) else 0) / (Fintype.card J : ℂ) *
      ((if x1 = x then (1:ℂ) else 0) / (Fintype.card J : ℂ)) = 1 / (Fintype.card J : ℂ) ^ 2 := by
    intro x
    rw [Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
    simp [sq]
  rw [Finset.sum_congr rfl fun x _ => hs x]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma qs5_reindex_psd {m n : Type} [Fintype m] [Fintype n] (e : m ≃ n) {A : Matrix m m ℂ}
    (hA : A.PosSemidef) : (Matrix.reindex e e A).PosSemidef := by
  simpa [Matrix.reindex_apply] using hA.submatrix e.symm

lemma qs5_reindex_mul {m n : Type} [Fintype m] [Fintype n] (e : m ≃ n) (A B : Matrix m m ℂ) :
    Matrix.reindex e e A * Matrix.reindex e e B = Matrix.reindex e e (A * B) := by
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

lemma qs5_reindex_trace {m n : Type} [Fintype m] [Fintype n] (e : m ≃ n) (A : Matrix m m ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

lemma qs5_reindex_sqrt {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) {A : Matrix m m ℂ} (hA : A.PosSemidef) :
    cfc Real.sqrt (Matrix.reindex e e A) = Matrix.reindex e e (cfc Real.sqrt A) := by
  apply qs5h_sqrt_unique (qs5_reindex_psd e (qs5h_sqrt_psd A))
  rw [qs5_reindex_mul, qs5h_sqrt_sq hA]

lemma qs5_traceNorm_reindex {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (M : Matrix m m ℂ) : traceNorm (Matrix.reindex e e M) = traceNorm M := by
  unfold traceNorm
  have h : (Matrix.reindex e e M)ᴴ = Matrix.reindex e e Mᴴ := by
    simp [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  rw [h, qs5_reindex_mul, qs5_reindex_sqrt e (Matrix.posSemidef_conjTranspose_mul_self M),
    qs5_reindex_trace]

lemma qs5_rootFid_reindex {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) {A B : Matrix m m ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    rootFidelity (Matrix.reindex e e A) (Matrix.reindex e e B) = rootFidelity A B := by
  unfold rootFidelity
  rw [qs5_reindex_sqrt e hA, qs5_reindex_mul, qs5_reindex_mul,
    qs5_reindex_sqrt e (qs5h_M_psd A B hB), qs5_reindex_trace]

lemma qs5tau_sqrt (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] :
    cfc Real.sqrt (qs5tau J) = qs5tau J :=
  qs5h_sqrt_unique (qs5tau_density J).1 (qs5tau_idem J)

lemma qs5_traceNorm_kron {J n : Type} [Fintype J] [DecidableEq J] [Nonempty J] [Fintype n]
    [DecidableEq n] (X : Matrix n n ℂ) : traceNorm (qs5tau J ⊗ₖ X) = traceNorm X := by
  unfold traceNorm
  have hτ := qs5tau_density J
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hτ.1.1.eq, qs5tau_idem,
    qs5h_sqrt_kron hτ.1 (Matrix.posSemidef_conjTranspose_mul_self X), qs5tau_sqrt,
    Matrix.trace_kronecker, hτ.2, one_mul]

lemma qs5_rootFid_kron {J n : Type} [Fintype J] [DecidableEq J] [Nonempty J] [Fintype n]
    [DecidableEq n] {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    rootFidelity (qs5tau J ⊗ₖ A) (qs5tau J ⊗ₖ B) = rootFidelity A B := by
  have hτ := qs5tau_density J
  show rootFidelity (Matrix.kronecker (qs5tau J) A) (Matrix.kronecker (qs5tau J) B) = _
  rw [qs5h_rootFid_kron hτ.1 hA hτ.1 hB]
  have : rootFidelity (qs5tau J) (qs5tau J) = 1 := by
    unfold rootFidelity
    rw [qs5tau_sqrt, qs5tau_idem, qs5tau_idem, qs5tau_sqrt, hτ.2]; simp
  rw [this, one_mul]

def qs5e (J I : Type) : (J × J) × (I × I) ≃ (J × I) × (J × I) := Equiv.prodProdProdComm J J I I

lemma qs5_choi_idT {J I : Type} [Fintype J] [DecidableEq J] [Nonempty J] [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E) :
    normalizedProcessState (idTensorSuperop (R := J) E) =
      Matrix.reindex (qs5e J I) (qs5e J I) (qs5tau J ⊗ₖ normalizedProcessState E) := by
  obtain ⟨m, A, hA, hEA⟩ := hE
  ext p q
  rcases p with ⟨⟨r, i⟩, ⟨s, k⟩⟩
  rcases q with ⟨⟨r', i'⟩, ⟨s', k'⟩⟩
  rw [qs5_choi_entry _ _ (qs5_idT_kraus (R := J) A E hEA)]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, qs5e, Equiv.prodProdProdComm_symm,
    Equiv.prodProdProdComm_apply, Matrix.kroneckerMap_apply, qs5tau_entry,
    qs5_choi_entry A E hEA, Matrix.one_apply, Fintype.card_prod, Nat.cast_mul]
  have hJ : (Fintype.card J : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hI : (Fintype.card I : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  by_cases h1 : s = r <;> by_cases h2 : s' = r' <;> simp [h1, h2]
  field_simp

theorem solution {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J]
    (delta : FiniteStateDistance) (hs : StateStable delta) (E F : FiniteProcess I I) :
    proDistance delta (idTensorSuperop (R := J) E.val) (idTensorSuperop (R := J) F.val) =
      proDistance delta E.val F.val ∧
    (∀ c : Choice, proDistance (stateDistance c) (idTensorSuperop (R := J) E.val)
      (idTensorSuperop (R := J) F.val) = proDistance (stateDistance c) E.val F.val) ∧
    proFidelity (idTensorSuperop (R := J) E.val) (idTensorSuperop (R := J) F.val) =
      proFidelity E.val F.val := by
  have dE := qs5_density _ E.2
  have dF := qs5_density _ F.2
  have dτ := qs5tau_density J
  have kE : IsDensityMatrix (qs5tau J ⊗ₖ normalizedProcessState E.val) :=
    ⟨dτ.1.kronecker dE.1, by rw [Matrix.trace_kronecker, dτ.2, dE.2, one_mul]⟩
  have kF : IsDensityMatrix (qs5tau J ⊗ₖ normalizedProcessState F.val) :=
    ⟨dτ.1.kronecker dF.1, by rw [Matrix.trace_kronecker, dτ.2, dF.2, one_mul]⟩
  have fid : fidelity (normalizedProcessState (idTensorSuperop (R := J) E.val))
      (normalizedProcessState (idTensorSuperop (R := J) F.val)) =
      fidelity (normalizedProcessState E.val) (normalizedProcessState F.val) := by
    unfold fidelity
    rw [qs5_choi_idT _ E.2, qs5_choi_idT _ F.2, qs5_rootFid_reindex _ kE.1 kF.1,
      qs5_rootFid_kron dE.1 dF.1]
  have td : traceDistance (normalizedProcessState (idTensorSuperop (R := J) E.val))
      (normalizedProcessState (idTensorSuperop (R := J) F.val)) =
      traceDistance (normalizedProcessState E.val) (normalizedProcessState F.val) := by
    unfold traceDistance
    rw [qs5_choi_idT _ E.2, qs5_choi_idT _ F.2]
    have hsub : ∀ A B : Matrix ((J × J) × (I × I)) ((J × J) × (I × I)) ℂ,
        Matrix.reindex (qs5e J I) (qs5e J I) A - Matrix.reindex (qs5e J I) (qs5e J I) B =
          Matrix.reindex (qs5e J I) (qs5e J I) (A - B) := by
      intro A B; ext; simp
    have hk : Matrix.kroneckerMap (· * ·) (qs5tau J) (normalizedProcessState E.val) -
        Matrix.kroneckerMap (· * ·) (qs5tau J) (normalizedProcessState F.val) =
        Matrix.kroneckerMap (· * ·) (qs5tau J)
          (normalizedProcessState E.val - normalizedProcessState F.val) := by
      ext; simp [mul_sub]
    rw [hsub, hk, qs5_traceNorm_reindex, qs5_traceNorm_kron]
  refine ⟨?_, ?_, fid⟩
  · unfold proDistance
    rw [qs5_choi_idT _ E.2, qs5_choi_idT _ F.2]
    have h2 := hs.2 _ _ (qs5e J I) ⟨_, kE⟩ ⟨_, kF⟩
    have h1 := hs.1 _ _ ⟨_, dE⟩ ⟨_, dF⟩ ⟨_, dτ⟩
    simp only at h1 h2
    exact h2.trans h1
  · intro c
    unfold proDistance
    cases c <;> simp only [stateDistance, td, fid]
