-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P17.proChaining
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:00:20.460658+00:00
-- url     : https://prove2.me/submissions/eb34ff73-cf7c-403a-8d66-ba09f26bd371

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17
noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P17

open scoped ComplexOrder MatrixOrder

lemma qc4_choi_entry {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {ι : Type} [Fintype ι]
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

lemma qc4_trace {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (hK : IsKrausFamily K) (E : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).trace = 1 := by
  have hd0 : (Fintype.card I : ℂ) ≠ 0 := by simp [Fintype.card_ne_zero]
  simp only [Matrix.trace, Matrix.diag, qc4_choi_entry K E hE]
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

lemma qc4_psd {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m : ℕ}
    (K : Fin m → Matrix I I ℂ) (E : Superop I I) (hE : ∀ ρ, E ρ = krausApply K ρ) :
    (normalizedProcessState E).PosSemidef := by
  have heq : normalizedProcessState E = (Fintype.card I : ℂ)⁻¹ •
      ∑ j, Matrix.vecMulVec (fun p : I × I => K j p.2 p.1) (star fun p : I × I => K j p.2 p.1) := by
    ext p q
    rw [qc4_choi_entry K E hE]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply, div_eq_inv_mul]
  rw [heq]
  refine Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ fun j _ =>
    Matrix.posSemidef_vecMulVec_self_star _) ?_
  exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le _)

lemma qc4_density {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (E : Superop I I)
    (hE : IsChannel E) : IsDensityMatrix (normalizedProcessState E) := by
  obtain ⟨m, K, hK, hEK⟩ := hE
  exact ⟨qc4_psd K _ hEK, qc4_trace K hK _ hEK⟩

lemma qc4_of_kraus {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] {ι : Type} [Fintype ι]
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

lemma qc4_comp {I : Type} [Fintype I] [DecidableEq I] {m n : ℕ}
    (A : Fin m → Matrix I I ℂ) (D : Fin n → Matrix I I ℂ) (E F : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply A ρ) (hF : ∀ ρ, F ρ = krausApply D ρ) :
    ∀ ρ, (E ∘ F) ρ = ∑ x : Fin m × Fin n, (A x.1 * D x.2) * ρ * (A x.1 * D x.2)ᴴ := by
  intro ρ
  simp only [Function.comp, hE, hF, krausApply, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]

lemma qc4_comp_channel {I : Type} [Fintype I] [DecidableEq I] (E F : Superop I I)
    (hE : IsChannel E) (hF : IsChannel F) : IsChannel (E ∘ F) := by
  obtain ⟨m, A, hA, hEA⟩ := hE
  obtain ⟨n, D, hD, hFD⟩ := hF
  refine qc4_of_kraus _ ?_ _ (qc4_comp A D E F hEA hFD)
  unfold IsKrausFamily at hA hD
  rw [Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_mul]
  calc ∑ x : Fin m, ∑ y : Fin n, (D y)ᴴ * (A x)ᴴ * (A x * D y)
      = ∑ y : Fin n, (D y)ᴴ * (∑ x : Fin m, (A x)ᴴ * A x) * D y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Matrix.mul_assoc]
    _ = 1 := by simp [hA, hD]

lemma qc4_sum_kron_left {I : Type} [Fintype I] [DecidableEq I] {n : ℕ} (X : Fin n → Matrix I I ℂ) :
    ∑ j, Matrix.kroneckerMap (· * ·) (1 : Matrix I I ℂ) (X j) =
      Matrix.kroneckerMap (· * ·) (1 : Matrix I I ℂ) (∑ j, X j) := by
  ext p q
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum]

lemma qc4_sum_kron_right {I : Type} [Fintype I] [DecidableEq I] {n : ℕ} (X : Fin n → Matrix I I ℂ) :
    ∑ j, Matrix.kroneckerMap (· * ·) (X j) (1 : Matrix I I ℂ) =
      Matrix.kroneckerMap (· * ·) (∑ j, X j) (1 : Matrix I I ℂ) := by
  ext p q
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

/-- id ⊗ E is a channel. -/
lemma qc4_idT_channel {I : Type} [Fintype I] [DecidableEq I] (E : Superop I I)
    (hE : IsChannel E) : IsChannel (idTensorSuperop (R := I) E) := by
  obtain ⟨m, A, hA, hEA⟩ := hE
  refine qc4_of_kraus (ι := Fin _) (fun j => Matrix.kroneckerMap (· * ·) (1 : Matrix I I ℂ) (A j)) ?_ _ ?_
  · unfold IsKrausFamily at hA
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
    rw [qc4_sum_kron_left, hA, Matrix.one_kronecker_one]
  · intro ρ
    ext p q
    simp only [idTensorSuperop, Matrix.of_apply, hEA, krausApply, Matrix.sum_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [Finset.sum_eq_single q.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp [Finset.sum_mul]

/-- The "transpose" channel on the first factor. -/
def qc4G {I : Type} [Fintype I] {n : ℕ} (D : Fin n → Matrix I I ℂ) : Superop (I × I) (I × I) :=
  fun Y => Matrix.of fun p q => ∑ j, ∑ a, ∑ b, D j a p.1 * Y (a, p.2) (b, q.2) * conj (D j b q.1)

lemma qc4G_channel {I : Type} [Fintype I] [DecidableEq I] {n : ℕ} (D : Fin n → Matrix I I ℂ)
    (hu : ∑ j, D j * (D j)ᴴ = 1) : IsChannel (qc4G D) := by
  refine qc4_of_kraus (ι := Fin _) (fun j => Matrix.kroneckerMap (· * ·) (D j)ᵀ (1 : Matrix I I ℂ)) ?_ _ ?_
  · simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
    rw [qc4_sum_kron_right]
    have : ∑ j, ((D j)ᵀ)ᴴ * (D j)ᵀ = 1 := by
      have h2 : ∀ j, ((D j)ᵀ)ᴴ * (D j)ᵀ = (D j * (D j)ᴴ)ᵀ := by
        intro j; ext a b; simp [Matrix.mul_apply, mul_comm]
      simp only [h2]
      rw [← Matrix.transpose_sum, hu, Matrix.transpose_one]
    rw [this, Matrix.one_kronecker_one]
  · intro ρ
    ext p q
    simp only [qc4G, Matrix.of_apply, Matrix.sum_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => enter [2, x]; rw [Finset.sum_eq_single q.2 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp [Finset.sum_mul]
    rw [Finset.sum_comm]

lemma qc4G_choi {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] {m n : ℕ}
    (A : Fin m → Matrix I I ℂ) (D : Fin n → Matrix I I ℂ) (E F : Superop I I)
    (hE : ∀ ρ, E ρ = krausApply A ρ) (hF : ∀ ρ, F ρ = krausApply D ρ) :
    qc4G D (normalizedProcessState E) = normalizedProcessState (E ∘ F) := by
  ext p q
  rw [qc4_choi_entry (fun x : Fin m × Fin n => A x.1 * D x.2) _ (qc4_comp A D E F hE hF)]
  simp only [qc4G, Matrix.of_apply, qc4_choi_entry A E hE]
  simp only [Fintype.sum_prod_type, Matrix.mul_apply, map_sum, map_mul, Finset.sum_div,
    Finset.mul_sum, Finset.sum_mul, mul_div_assoc']
  conv_lhs => enter [2, j, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, k, 2, j]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (delta : FiniteStateDistance)
    (hm : StateMetrics delta)
    (hc : StateContractive delta) (E1 F1 E2 F2 : FiniteProcess I I) (hu : F1.val 1 = 1) :
    proDistance delta (E2.val ∘ E1.val) (F2.val ∘ F1.val) ≤
      proDistance delta E2.val F2.val + proDistance delta E1.val F1.val := by
  have dn : ∀ E : Superop I I, IsChannel E →
      IsDensityMatrix (normalizedProcessState E) := fun E h => qc4_density E h
  let S : ∀ E : Superop I I, IsChannel E → ProcessDensityInput (I × I) :=
    fun E h => ⟨_, dn E h⟩
  have tri := (hm (I × I)).2.2.2 (S _ (qc4_comp_channel _ _ E2.2 E1.2))
    (S _ (qc4_comp_channel _ _ E2.2 F1.2)) (S _ (qc4_comp_channel _ _ F2.2 F1.2))
  simp only [S] at tri
  -- term 1
  have t1 := hc (I × I) (I × I) ⟨_, qc4_idT_channel _ E2.2⟩ (S _ E1.2) (S _ F1.2)
  simp only [S] at t1
  have e1 : ∀ X : Superop I I, idTensorSuperop (R := I) E2.val (normalizedProcessState X) =
      normalizedProcessState (E2.val ∘ X) := fun X => rfl
  rw [e1, e1] at t1
  -- term 2
  obtain ⟨n, D, hD, hFD⟩ := F1.2
  have hu' : ∑ j, D j * (D j)ᴴ = 1 := by
    rw [← hu, hFD]; simp [krausApply]
  have t2 := hc (I × I) (I × I) ⟨_, qc4G_channel D hu'⟩ (S _ E2.2) (S _ F2.2)
  simp only [S] at t2
  obtain ⟨m, A, hA, hEA⟩ := E2.2
  obtain ⟨m', B, hB, hFB⟩ := F2.2
  rw [qc4G_choi A D _ _ hEA hFD, qc4G_choi B D _ _ hFB hFD] at t2
  unfold proDistance
  linarith
