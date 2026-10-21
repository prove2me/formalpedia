-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P14.relabel_replacement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:49:21.326894+00:00
-- url     : https://prove2.me/submissions/bf3d24d0-7015-4f53-90cb-acb7bfd5e2a2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P14
noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms QAlgorithms.QuditFidelity QAlgorithms.Papers.Independent.Claimed50.P14

/-- relabeling map on (labels, inputs) -/
def g59c_f {d n : ℕ} (σ : Equiv.Perm (Fin d)) (p : Labels d n × Labels d n) : Labels d n × Labels d n :=
  (σ ∘ p.1, p.2)

theorem g59c_causal_relabel {d : ℕ} (σ : Equiv.Perm (Fin d)) : ∀ (n : ℕ)
    (A : Matrix (Labels d n × Labels d n) (Labels d n × Labels d n) ℂ),
    CausalTraining d 0 n A → CausalTraining d 0 n (A.submatrix (g59c_f σ) (g59c_f σ)) := by
  intro n
  induction n with
  | zero =>
    intro A hA
    simp only [CausalTraining] at hA ⊢
    subst hA
    ext p q
    have : ∀ p q : Labels d 0 × Labels d 0, p = q := fun p q => Subsingleton.elim _ _
    simp only [Matrix.submatrix_apply, Matrix.one_apply]
    rw [if_pos (this _ _), if_pos (this _ _)]
  | succ n ih =>
    intro A hA
    simp only [CausalTraining, Nat.not_succ_le_zero, if_false] at hA ⊢
    refine ⟨hA.1.submatrix _, ?_⟩
    obtain ⟨B, C, hB, hC, hAB, hBC⟩ := hA.2
    refine ⟨B.submatrix (fun p => (p.1, g59c_f σ p.2)) (fun p => (p.1, g59c_f σ p.2)),
      C.submatrix (g59c_f σ) (g59c_f σ), hB.submatrix _, ih C hC, fun j a l b => ?_, fun j a l b => ?_⟩
    · simp only [Matrix.submatrix_apply, g59c_f, hAB, Function.comp_apply,
        EmbeddingLike.apply_eq_iff_eq]
      rfl
    · simp only [Matrix.submatrix_apply, g59c_f, ← hBC]

theorem g59c_causal_avg {d : ℕ} {ι : Type} [Fintype ι] [Nonempty ι] : ∀ (n : ℕ)
    (A : ι → Matrix (Labels d n × Labels d n) (Labels d n × Labels d n) ℂ),
    (∀ x, CausalTraining d 0 n (A x)) →
      CausalTraining d 0 n (((Fintype.card ι : ℂ)⁻¹) • ∑ x, A x) := by
  have hc : (Fintype.card ι : ℂ) ≠ 0 := by
    have := Fintype.card_pos (α := ι); exact_mod_cast this.ne'
  have hc0 : (0 : ℂ) ≤ (Fintype.card ι : ℂ)⁻¹ := by
    rw [show ((Fintype.card ι : ℂ)⁻¹) = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
    exact_mod_cast (by positivity : (0:ℝ) ≤ (Fintype.card ι : ℝ)⁻¹)
  intro n
  induction n with
  | zero =>
    intro A hA
    simp only [CausalTraining] at hA ⊢
    simp only [hA, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  | succ n ih =>
    intro A hA
    simp only [CausalTraining, Nat.not_succ_le_zero, if_false] at hA ⊢
    refine ⟨Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ (fun x _ => (hA x).1)) hc0, ?_⟩
    choose B C hB hC hAB hBC using fun x => (hA x).2
    refine ⟨((Fintype.card ι : ℂ)⁻¹) • ∑ x, B x, ((Fintype.card ι : ℂ)⁻¹) • ∑ x, C x,
      Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ (fun x _ => hB x)) hc0, ih C hC,
      fun j a l b => ?_, fun j a l b => ?_⟩
    · simp only [Matrix.smul_apply, Matrix.sum_apply, hAB, smul_eq_mul]
      split_ifs <;> simp
    · simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, ← Finset.mul_sum, ← hBC]
      rw [Finset.sum_comm]

def g59c_E {d N : ℕ} (σ : Equiv.Perm (Fin d)) : TrainingWires d N ≃ TrainingWires d N :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.piCongrRight (fun _ => σ)) (Equiv.refl _))

lemma g59c_E_apply {d N : ℕ} (σ : Equiv.Perm (Fin d)) (x : TrainingWires d N) :
    g59c_E σ x = (x.1, (σ ∘ x.2.1, x.2.2)) := rfl

lemma g59c_avg_i {d N : ℕ} (R : Branches d N) (i : Fin d) :
    relabelAverage R i = ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) •
      ∑ σ : Equiv.Perm (Fin d), (R (σ i)).submatrix (g59c_E σ) (g59c_E σ) := by
  unfold relabelAverage
  rw [Pi.smul_apply, Finset.sum_apply]
  rfl

lemma g59c_avg_apply {d N : ℕ} (R : Branches d N) (i : Fin d) (x y : TrainingWires d N) :
    relabelAverage R i x y = ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) *
      ∑ σ : Equiv.Perm (Fin d), R (σ i) (g59c_E σ x) (g59c_E σ y) := by
  rw [g59c_avg_i, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rfl

lemma g59c_c0 (d : ℕ) : (0 : ℂ) ≤ ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) := by
  rw [show ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) =
    (((Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  exact_mod_cast (by positivity : (0:ℝ) ≤ (Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹)

lemma g59c_avg_LI {d N : ℕ} (S : Branches d N) (hS : LearningInstrument 0 S) :
    LearningInstrument 0 (relabelAverage S) := by
  obtain ⟨hpsd, A, hA, hsum⟩ := hS
  refine ⟨fun i => ?_, ((Fintype.card (Equiv.Perm (Fin d)) : ℂ)⁻¹) •
      ∑ σ : Equiv.Perm (Fin d), A.submatrix (g59c_f σ) (g59c_f σ), ?_, ?_⟩
  · rw [g59c_avg_i]
    exact Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ (fun σ _ => (hpsd _).submatrix _)) (g59c_c0 d)
  · exact g59c_causal_avg N _ (fun σ => g59c_causal_relabel σ N A hA)
  · intro t j a s l b
    simp only [g59c_avg_apply]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have : ∀ σ : Equiv.Perm (Fin d), (∑ i, S (σ i) (g59c_E σ (t, j, a)) (g59c_E σ (s, l, b))) =
        if t = s then A.submatrix (g59c_f σ) (g59c_f σ) (j, a) (l, b) else 0 := by
      intro σ
      rw [Equiv.sum_comp σ (fun i => S i (g59c_E σ (t, j, a)) (g59c_E σ (s, l, b)))]
      simp only [g59c_E_apply, hsum]
      rfl
    simp only [this, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    split_ifs <;> simp

lemma g59c_avg_diag {d N : ℕ} (S : Branches d N) (hdiag : IsDiagonal S) :
    IsDiagonal (relabelAverage S) := by
  unfold IsDiagonal
  funext i x y
  unfold outcomeDephasing
  split_ifs with h
  · rfl
  · rw [g59c_avg_apply]
    have : ∀ σ : Equiv.Perm (Fin d), S (σ i) (g59c_E σ x) (g59c_E σ y) = 0 := by
      intro σ
      rw [hdiag]
      unfold outcomeDephasing
      rw [if_neg]
      simp only [g59c_E_apply]
      intro h'
      exact h ((Equiv.injective σ).comp_left h')
    simp [this]

lemma g59c_cR_E {d N : ℕ} (σ : Equiv.Perm (Fin d)) (U : Matrix (Fin d) (Fin d) ℂ) :
    (covariantRepresentation (N := N) U).submatrix (g59c_E σ) (g59c_E σ) = covariantRepresentation U := by
  ext x y
  simp only [Matrix.submatrix_apply, g59c_E_apply, covariantRepresentation]
  have : (σ ∘ x.2.1 = σ ∘ y.2.1) ↔ x.2.1 = y.2.1 :=
    ⟨fun h => (Equiv.injective σ).comp_left h, fun h => by rw [h]⟩
  simp only [this]

lemma g59c_avg_cov {d N : ℕ} (S : Branches d N) (hcov : IsLearningCovariant S) :
    IsLearningCovariant (relabelAverage S) := by
  intro U i
  rw [g59c_avg_i, Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  conv_lhs => rw [← g59c_cR_E σ]
  conv_rhs => rw [← g59c_cR_E σ]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hcov U (σ i)]

lemma g59c_avg_inv {d N : ℕ} (S : Branches d N) : IsRelabelInvariant (relabelAverage S) := by
  intro τ
  funext i
  ext x y
  simp only [relabelClassical]
  rw [g59c_avg_apply, g59c_avg_apply]
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight τ)]
  rfl

lemma g59c_P_apply {d : ℕ} (σ : Equiv.Perm (Fin d)) (z y : Fin d) :
    σ.permMatrix ℂ z y = if σ z = y then 1 else 0 := by
  simp [PEquiv.toMatrix_apply]

lemma g59c_omega {d : ℕ} (hd : 0 < d) (σ : Equiv.Perm (Fin d)) :
    ∃ ω : ℂ, conj ω * ω = 1 ∧ ω ^ d * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · exact ⟨1, by simp, by simp [h]⟩
  · refine ⟨Complex.exp (Real.pi * Complex.I / d), ?_, ?_⟩
    · rw [← Complex.exp_conj, ← Complex.exp_add]
      have : (starRingEnd ℂ) (↑Real.pi * Complex.I / ↑d) + ↑Real.pi * Complex.I / ↑d = 0 := by
        simp [map_div₀, Complex.conj_ofReal, Complex.conj_I]; ring
      rw [this, Complex.exp_zero]
    · rw [← Complex.exp_nat_mul, h]
      have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      rw [show (d : ℂ) * (↑Real.pi * Complex.I / ↑d) = Real.pi * Complex.I by field_simp,
        Complex.exp_pi_mul_I]
      simp

lemma g59c_W_ex {d : ℕ} (hd : 0 < d) (σ : Equiv.Perm (Fin d)) :
    ∃ W : SU d, ∃ ω : ℂ, conj ω * ω = 1 ∧ (W : Matrix (Fin d) (Fin d) ℂ) = ω • σ.permMatrix ℂ := by
  obtain ⟨ω, h1, h2⟩ := g59c_omega hd σ
  have hu : ω • σ.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_permMatrix,
      smul_mul_smul_comm, ← Matrix.permMatrix_mul]
    simp only [mul_inv_cancel, Matrix.permMatrix_one]
    rw [show star ω = conj ω from rfl, h1, one_smul]
  have hdet : (ω • σ.permMatrix ℂ).det = 1 := by
    rw [Matrix.det_smul, Matrix.det_permutation, Fintype.card_fin]
    simpa using h2
  exact ⟨⟨_, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hu, hdet⟩⟩, ω, h1, rfl⟩

def g59c_h {d N : ℕ} (σ : Equiv.Perm (Fin d)) : TrainingWires d N ≃ TrainingWires d N :=
  Equiv.prodCongr σ (Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight (fun _ => σ)))

lemma g59c_h_apply {d N : ℕ} (σ : Equiv.Perm (Fin d)) (x : TrainingWires d N) :
    g59c_h σ x = (σ x.1, (x.2.1, σ ∘ x.2.2)) := rfl

lemma g59c_cR_W {d N : ℕ} (σ : Equiv.Perm (Fin d)) (ω : ℂ) (x y : TrainingWires d N) :
    covariantRepresentation (ω • σ.permMatrix ℂ) x y =
      (conj ω * ω ^ N) * (if y = g59c_h σ x then 1 else 0) := by
  rcases x with ⟨t, j, a⟩; rcases y with ⟨s, l, b⟩
  simp only [covariantRepresentation, inputTensorPower, Matrix.smul_apply, smul_eq_mul,
    g59c_P_apply, g59c_h_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_boole]
  simp only [Prod.mk.injEq]
  have hb : (∀ n ∈ Finset.univ, σ (a n) = b n) ↔ b = σ ∘ a :=
    ⟨fun h => funext fun n => (h n (Finset.mem_univ _)).symm, fun h n _ => by rw [h]; rfl⟩
  simp only [hb]
  by_cases h1 : j = l
  · subst h1
    by_cases h2 : σ t = s
    · subst h2; by_cases h3 : b = σ ∘ a <;> simp [h3]
    · simp [h2, Ne.symm h2]
  · simp [h1, Ne.symm h1]

lemma g59c_comm_inv {d N : ℕ} (M : Matrix (TrainingWires d N) (TrainingWires d N) ℂ)
    (σ : Equiv.Perm (Fin d)) (ω : ℂ) (hω : conj ω * ω = 1)
    (hM : M * covariantRepresentation (ω • σ.permMatrix ℂ) =
      covariantRepresentation (ω • σ.permMatrix ℂ) * M) (x y : TrainingWires d N) :
    M (g59c_h σ x) (g59c_h σ y) = M x y := by
  have hk : conj ω * ω ^ N ≠ 0 := by
    intro h
    have hω0 : ω ≠ 0 := by intro h0; rw [h0] at hω; simp at hω
    rcases mul_eq_zero.mp h with h | h
    · apply hω0; simpa using h
    · exact hω0 (pow_eq_zero_iff'.mp h).1
  have e := congrFun (congrFun hM x) (g59c_h σ y)
  simp only [Matrix.mul_apply, g59c_cR_W] at e
  have inj : ∀ z, (g59c_h σ y = g59c_h σ z) ↔ (z = y) :=
    fun z => ⟨fun h => ((g59c_h σ).injective h).symm, fun h => by rw [h]⟩
  simp only [inj, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at e
  exact (mul_left_cancel₀ hk ((mul_comm _ _).trans e)).symm

lemma g59c_rp1 {d N : ℕ} (R : Branches d N) (i t s : Fin d) :
    replicatedPOVM R 1 i t s = ∑ j, R i (s, (j, j)) (t, (j, j)) := by
  simp only [replicatedPOVM, inputTensorPower, Matrix.one_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hf : ∀ a : Labels d N, (∀ n ∈ Finset.univ, a n = j n) ↔ a = j :=
    fun a => ⟨fun h => funext fun n => h n (Finset.mem_univ _), fun h n _ => by rw [h]⟩
  simp only [Finset.prod_boole, hf]
  simp only [ apply_ite (starRingEnd ℂ), map_one, map_zero, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma g59c_part4 {d N : ℕ} (hd : 0 < d) (R : Branches d N) (hcov : IsLearningCovariant R)
    (hinv : IsRelabelInvariant R) (σ : Equiv.Perm (Fin d)) (i a b : Fin d) :
    replicatedPOVM R 1 (σ i) (σ a) (σ b) = replicatedPOVM R 1 i a b := by
  obtain ⟨W, ω, hω, hW⟩ := g59c_W_ex hd σ
  have hc := hcov W (σ i)
  rw [hW] at hc
  rw [g59c_rp1, g59c_rp1]
  rw [← Equiv.sum_comp (Equiv.piCongrRight (fun _ => σ) : Labels d N ≃ Labels d N)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h1 := g59c_comm_inv (R (σ i)) σ ω hω hc (b, (σ ∘ j, j)) (a, (σ ∘ j, j))
  have h2 := congrFun (congrFun (congrFun (hinv σ) i) (b, (j, j))) (a, (j, j))
  simp only [g59c_h_apply, relabelClassical] at h1 h2
  rw [h2, ← h1]
  rfl

instance g59c_prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

instance g59c_haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

instance g59c_suprob (d : ℕ) : IsProbabilityMeasure (specialUnitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

instance g59c_suhaar (d : ℕ) : (specialUnitaryHaar d).IsHaarMeasure := by
  unfold specialUnitaryHaar; infer_instance

theorem g59c_su_right (d : ℕ) (g : SU d) :
    Measure.map (· * g) (specialUnitaryHaar d) = specialUnitaryHaar d := by
  haveI : IsProbabilityMeasure (Measure.map (· * g) (specialUnitaryHaar d)) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

instance g59c_surinv (d : ℕ) : (specialUnitaryHaar d).IsMulRightInvariant :=
  ⟨fun g => g59c_su_right d g⟩

theorem g59c_cc {d : ℕ} (i j : Fin d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => (U : Matrix (Fin d) (Fin d) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem g59c_scc {d : ℕ} (i j : Fin d) :
    Continuous (fun U : SU d => (U : Matrix (Fin d) (Fin d) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

def g59c_q {n : ℕ} (i0 : Fin n) (D : Matrix (Fin n) (Fin n) ℂ) (U : Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  (∑ a, ∑ b, conj ((U : Matrix (Fin n) (Fin n) ℂ) a i0) * D a b * (U : Matrix (Fin n) (Fin n) ℂ) b i0).re

theorem g59c_pd {n : ℕ} (hh : 0 < n) (D : Matrix (Fin n) (Fin n) ℂ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    effectProb D (pureDensity (act (U : Matrix (Fin n) (Fin n) ℂ) (ket ⟨0, hh⟩))) = g59c_q ⟨0, hh⟩ D U := by
  simp only [effectProb, pureDensity, act, ket, g59c_q, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.of_apply, Matrix.mulVec, dotProduct]
  simp only [PiLp.ofLp_single, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem g59c_dist {n m : ℕ} (hh : 0 < n) (P Q : Fin m → Matrix (Fin n) (Fin n) ℂ) :
    povmDistance hh P Q = ∫ U, ∑ i, (g59c_q ⟨0, hh⟩ (P i - Q i) U) ^ 2 ∂QAlgorithms.Schur.unitaryHaar n := by
  unfold povmDistance haarPureStateLaw
  have hc : Continuous (fun psi : EuclideanSpace ℂ (Fin n) =>
      ∑ i, (effectProb (P i - Q i) (pureDensity psi)) ^ 2) := by
    unfold effectProb pureDensity; fun_prop
  rw [integral_map (haarState_continuous n hh).measurable.aemeasurable hc.aestronglyMeasurable]
  simp only [g59c_pd]

theorem g59c_intc {n : ℕ} {f : Matrix.unitaryGroup (Fin n) ℂ → ℝ} (hf : Continuous f) :
    Integrable f (QAlgorithms.Schur.unitaryHaar n) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem g59c_sintc {d : ℕ} {f : SU d → ℝ} (hf : Continuous f) :
    Integrable f (specialUnitaryHaar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem g59c_q_jcont {d : ℕ} (i0 : Fin d) (D : SU d → Matrix (Fin d) (Fin d) ℂ)
    (hD : ∀ a b, Continuous fun U => D U a b) :
    Continuous (fun p : SU d × Matrix.unitaryGroup (Fin d) ℂ => g59c_q i0 (D p.1) p.2) := by
  unfold g59c_q
  exact Complex.continuous_re.comp (continuous_finsetSum _ (fun a _ => continuous_finsetSum _ (fun b _ =>
    ((Complex.continuous_conj.comp ((g59c_cc a i0).comp continuous_snd)).mul
      ((hD a b).comp continuous_fst)).mul ((g59c_cc b i0).comp continuous_snd))))

theorem g59c_rp_cont {d N : ℕ} (R : Branches d N) (i t s : Fin d) :
    Continuous (fun U : SU d => replicatedPOVM R (U : Matrix (Fin d) (Fin d) ℂ) i t s) := by
  unfold replicatedPOVM inputTensorPower
  refine continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun a _ =>
    continuous_finsetSum _ (fun b _ => ?_)))
  exact ((Complex.continuous_conj.comp (continuous_finset_prod _ (fun n _ => g59c_scc _ _))).mul
    continuous_const).mul (continuous_finset_prod _ (fun n _ => g59c_scc _ _))

theorem g59c_mf_cont {d : ℕ} (i t s : Fin d) :
    Continuous (fun U : SU d => measurementFamily (U : Matrix (Fin d) (Fin d) ℂ) i t s) := by
  unfold measurementFamily
  exact (g59c_scc t i).mul (Complex.continuous_conj.comp (g59c_scc s i))

/-- the integrand -/
def g59c_phi {d N : ℕ} (hd : 0 < d) (R : Branches d N) (U : SU d) (V : Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  ∑ i, (g59c_q ⟨0, hd⟩ (measurementFamily (U : Matrix (Fin d) (Fin d) ℂ) i -
    replicatedPOVM R (U : Matrix (Fin d) (Fin d) ℂ) i) V) ^ 2

theorem g59c_phi_cont {d N : ℕ} (hd : 0 < d) (R : Branches d N) :
    Continuous (fun p : SU d × Matrix.unitaryGroup (Fin d) ℂ => g59c_phi hd R p.1 p.2) := by
  unfold g59c_phi
  refine continuous_finsetSum _ (fun i _ => ?_)
  have hD : ∀ a b, Continuous fun U : SU d => (measurementFamily (U : Matrix (Fin d) (Fin d) ℂ) i -
      replicatedPOVM R (U : Matrix (Fin d) (Fin d) ℂ) i) a b := fun a b =>
    (g59c_mf_cont i a b).sub (g59c_rp_cont R i a b)
  have := g59c_q_jcont ⟨0, hd⟩ (fun U : SU d => measurementFamily (U : Matrix (Fin d) (Fin d) ℂ) i -
      replicatedPOVM R (U : Matrix (Fin d) (Fin d) ℂ) i) hD
  exact this.pow 2

instance g59c_fc (d : ℕ) : FirstCountableTopology (Matrix (Fin d) (Fin d) ℂ) :=
  inferInstanceAs (FirstCountableTopology (Fin d → Fin d → ℂ))

instance g59c_fcs (d : ℕ) : FirstCountableTopology (SU d) :=
  firstCountableTopology_induced _ (Matrix (Fin d) (Fin d) ℂ) Subtype.val

theorem g59c_inner_cont {d N : ℕ} (hd : 0 < d) (R : Branches d N) :
    Continuous (fun U : SU d => ∫ V, g59c_phi hd R U V ∂QAlgorithms.Schur.unitaryHaar d) := by
  have := continuous_parametric_integral_of_continuous (μ := QAlgorithms.Schur.unitaryHaar d)
    (f := fun U V => g59c_phi hd R U V) (g59c_phi_cont hd R) (s := Set.univ) isCompact_univ
  simpa only [Measure.restrict_univ] using this

theorem g59c_LD {d N : ℕ} (hd : 0 < d) (R : Branches d N) :
    learningDistance hd R = ∫ U, ∫ V, g59c_phi hd R U V ∂QAlgorithms.Schur.unitaryHaar d ∂specialUnitaryHaar d := by
  unfold learningDistance
  congr 1
  funext U
  rw [g59c_dist]
  rfl

lemma g59c_mul_P {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (ω : ℂ) (σ : Equiv.Perm (Fin d)) (x y : Fin d) :
    (U * (ω • σ.permMatrix ℂ)) x y = ω * U x (σ.symm y) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm y)]
  · simp [Matrix.smul_apply, g59c_P_apply]; ring
  · intro z _ hz
    have : σ z ≠ y := fun h => hz (by rw [← h]; simp)
    simp [Matrix.smul_apply, g59c_P_apply, this]
  · simp

lemma g59c_itp {d N : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (ω : ℂ) (σ : Equiv.Perm (Fin d))
    (a j : Labels d N) :
    inputTensorPower (U * (ω • σ.permMatrix ℂ)) a j =
      ω ^ N * inputTensorPower U a (fun n => σ.symm (j n)) := by
  simp only [inputTensorPower, g59c_mul_P, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

lemma g59c_rp_rel {d N : ℕ} (R : Branches d N) (σ : Equiv.Perm (Fin d)) (U : Matrix (Fin d) (Fin d) ℂ)
    (ω : ℂ) (hω : conj ω * ω = 1) (i : Fin d) :
    replicatedPOVM (relabelClassical R σ) U i =
      replicatedPOVM R (U * (ω • σ.permMatrix ℂ)) (σ i) := by
  ext t s
  simp only [replicatedPOVM, g59c_itp]
  refine Fintype.sum_equiv (Equiv.piCongrRight (fun _ => σ) : Labels d N ≃ Labels d N) _ _ (fun j => ?_)
  have hj : ((Equiv.piCongrRight (fun _ => σ) : Labels d N ≃ Labels d N) j) = σ ∘ j := rfl
  have hj2 : (fun n => σ.symm ((σ ∘ j) n)) = j := by funext n; simp
  rw [hj, hj2]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp only [map_mul, map_pow, relabelClassical]
  have : conj ω ^ N * ω ^ N = 1 := by rw [← mul_pow, hω, one_pow]
  linear_combination (-(conj (inputTensorPower U a j) * R (σ i) (s, σ ∘ j, a) (t, σ ∘ j, b) *
    inputTensorPower U b j)) * this

lemma g59c_mf_rel {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (ω : ℂ) (hω : conj ω * ω = 1)
    (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    measurementFamily (U * (ω • σ.permMatrix ℂ)) (σ i) = measurementFamily U i := by
  ext a b
  simp only [measurementFamily, g59c_mul_P, Equiv.symm_apply_apply, map_mul]
  linear_combination (U a i * conj (U b i)) * hω

lemma g59c_pd_perm {h m : ℕ} (hh : 0 < h) (P Q : Fin m → Matrix (Fin h) (Fin h) ℂ)
    (σ : Equiv.Perm (Fin m)) :
    povmDistance hh (fun i => P (σ i)) (fun i => Q (σ i)) = povmDistance hh P Q := by
  unfold povmDistance
  congr 1
  funext ψ
  exact Equiv.sum_comp σ (fun i => (effectProb (P i - Q i) (pureDensity ψ)) ^ 2)

set_option maxHeartbeats 1000000 in
lemma g59c_LD_rel {d N : ℕ} (hd : 0 < d) (R : Branches d N) (σ : Equiv.Perm (Fin d)) :
    learningDistance hd (relabelClassical R σ) = learningDistance hd R := by
  obtain ⟨W, ω, hω, hW⟩ := g59c_W_ex hd σ
  unfold learningDistance
  set G : SU d → ℝ := fun U => povmDistance hd (measurementFamily (U : Matrix (Fin d) (Fin d) ℂ))
    (replicatedPOVM R (U : Matrix (Fin d) (Fin d) ℂ)) with hG
  have key : ∀ U : SU d, povmDistance hd (measurementFamily (U : Matrix (Fin d) (Fin d) ℂ))
      (replicatedPOVM (relabelClassical R σ) (U : Matrix (Fin d) (Fin d) ℂ)) = G (U * W) := by
    intro U
    have hc : ((U * W : SU d) : Matrix (Fin d) (Fin d) ℂ) =
        (U : Matrix (Fin d) (Fin d) ℂ) * (ω • σ.permMatrix ℂ) := by rw [← hW]; rfl
    set M : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ) * (ω • σ.permMatrix ℂ) with hM
    have e1 : (fun i => measurementFamily M (σ i)) = measurementFamily (U : Matrix (Fin d) (Fin d) ℂ) :=
      funext fun i => g59c_mf_rel _ ω hω σ i
    have e2 : (fun i => replicatedPOVM R M (σ i)) =
        replicatedPOVM (relabelClassical R σ) (U : Matrix (Fin d) (Fin d) ℂ) :=
      funext fun i => (g59c_rp_rel R σ _ ω hω i).symm
    simp only [hG]
    rw [hc, ← g59c_pd_perm hd (measurementFamily M) (replicatedPOVM R M) σ, e1, e2]
  have h2 : (fun U : SU d => povmDistance hd (measurementFamily (U : Matrix (Fin d) (Fin d) ℂ))
      (replicatedPOVM (relabelClassical R σ) (U : Matrix (Fin d) (Fin d) ℂ))) = fun U => G (U * W) :=
    funext key
  rw [h2]
  exact integral_mul_right_eq_self G W

lemma g59c_rp_avg {d N : ℕ} (R : Branches d N) (U : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    replicatedPOVM (relabelAverage R) U i =
      ((((Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹ : ℝ)) : ℂ) •
        ∑ σ, replicatedPOVM (relabelClassical R σ) U i := by
  ext t s
  simp only [replicatedPOVM, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, g59c_avg_apply,
    relabelClassical, g59c_E_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun x => (x.2.2.2, x.1, x.2.1, x.2.2.1)
      invFun := fun y => (y.2.1, y.2.2.1, y.2.2.2, y.1)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]
  push_cast; ring

lemma g59c_q_lin {n : ℕ} {ι : Type} [Fintype ι] (i0 : Fin n) (c : ℝ) (D : ι → Matrix (Fin n) (Fin n) ℂ)
    (V : Matrix.unitaryGroup (Fin n) ℂ) :
    g59c_q i0 ((c : ℂ) • ∑ σ, D σ) V = c * ∑ σ, g59c_q i0 (D σ) V := by
  unfold g59c_q
  rw [← Complex.re_sum, ← Complex.re_ofReal_mul]
  congr 1
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun x => (x.2.2, x.1, x.2.1)
      invFun := fun y => (y.2.1, y.2.2, y.1)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]
  ring

lemma g59c_phi_nonneg {d N : ℕ} (hd : 0 < d) (R : Branches d N) (U : SU d) (V : Matrix.unitaryGroup (Fin d) ℂ) :
    0 ≤ g59c_phi hd R U V :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

lemma g59c_key {d N : ℕ} (hd : 0 < d) (S : Branches d N) (U : SU d) (V : Matrix.unitaryGroup (Fin d) ℂ) :
    g59c_phi hd (relabelAverage S) U V ≤
      ((Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹) * ∑ σ, g59c_phi hd (relabelClassical S σ) U V := by
  set n : ℝ := (Fintype.card (Equiv.Perm (Fin d)) : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hdiff : ∀ i, measurementFamily (U : Matrix (Fin d) (Fin d) ℂ) i -
      replicatedPOVM (relabelAverage S) (U : Matrix (Fin d) (Fin d) ℂ) i =
      ((n⁻¹ : ℝ) : ℂ) • ∑ σ : Equiv.Perm (Fin d), (measurementFamily (U : Matrix (Fin d) (Fin d) ℂ) i -
        replicatedPOVM (relabelClassical S σ) (U : Matrix (Fin d) (Fin d) ℂ) i) := by
    intro i
    rw [g59c_rp_avg, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ, ← hn]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have : ((n⁻¹ : ℝ) : ℂ) * ((Fintype.card (Equiv.Perm (Fin d)) : ℕ) : ℂ) = 1 := by
      rw [show ((Fintype.card (Equiv.Perm (Fin d)) : ℕ) : ℂ) = ((n : ℝ) : ℂ) by rw [hn]; push_cast; rfl]
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hn0.ne', Complex.ofReal_one]
    rw [this, one_smul]
  unfold g59c_phi
  simp only [hdiff, g59c_q_lin]
  conv_rhs => rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Equiv.Perm (Fin d))))
    (f := fun σ => g59c_q ⟨0, hd⟩ (measurementFamily (U : Matrix (Fin d) (Fin d) ℂ) i -
        replicatedPOVM (relabelClassical S σ) (U : Matrix (Fin d) (Fin d) ℂ) i) V)
  rw [Finset.card_univ, ← hn] at h
  rw [mul_pow]
  calc (n⁻¹) ^ 2 * (∑ σ, _) ^ 2 ≤ (n⁻¹) ^ 2 * (n * ∑ σ, _) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

lemma g59c_hV {d N : ℕ} (hd : 0 < d) (R : Branches d N) (U : SU d) :
    Integrable (fun V => g59c_phi hd R U V) (QAlgorithms.Schur.unitaryHaar d) := by
  have h1 : Continuous (fun V : Matrix.unitaryGroup (Fin d) ℂ =>
      ((U, V) : SU d × Matrix.unitaryGroup (Fin d) ℂ)) :=
    Continuous.prodMk continuous_const continuous_id
  have h2 := (g59c_phi_cont hd R).comp h1
  exact g59c_intc h2

lemma g59c_stepA {d N : ℕ} (hd : 0 < d) (S : Branches d N) (U : SU d) :
    ∫ V, g59c_phi hd (relabelAverage S) U V ∂QAlgorithms.Schur.unitaryHaar d ≤
      ((Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹) *
        ∑ σ, ∫ V, g59c_phi hd (relabelClassical S σ) U V ∂QAlgorithms.Schur.unitaryHaar d := by
  rw [← integral_finset_sum _ (fun σ _ => g59c_hV hd _ U), ← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun V => g59c_phi_nonneg hd _ U V)
  · exact (integrable_finset_sum _ (fun σ _ => g59c_hV hd _ U)).const_mul _
  · exact Filter.Eventually.of_forall (fun V => g59c_key hd S U V)

lemma g59c_stepB {d N : ℕ} (hd : 0 < d) (S : Branches d N) :
    learningDistance hd (relabelAverage S) ≤
      ∫ U, ((Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹) *
        ∑ σ, ∫ V, g59c_phi hd (relabelClassical S σ) U V ∂QAlgorithms.Schur.unitaryHaar d
        ∂specialUnitaryHaar d := by
  rw [g59c_LD]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun U => integral_nonneg (fun V => g59c_phi_nonneg hd _ U V))
  · exact g59c_sintc (continuous_const.mul (continuous_finsetSum _ (fun σ _ => g59c_inner_cont hd _)))
  · exact Filter.Eventually.of_forall (fun U => g59c_stepA hd S U)

lemma g59c_stepC {d N : ℕ} (hd : 0 < d) (S : Branches d N) :
    ∫ U, ((Fintype.card (Equiv.Perm (Fin d)) : ℝ)⁻¹) *
        ∑ σ, ∫ V, g59c_phi hd (relabelClassical S σ) U V ∂QAlgorithms.Schur.unitaryHaar d
        ∂specialUnitaryHaar d = learningDistance hd S := by
  rw [integral_const_mul, integral_finset_sum _ (fun σ _ => g59c_sintc (g59c_inner_cont hd _))]
  have : ∀ σ : Equiv.Perm (Fin d), ∫ U, ∫ V, g59c_phi hd (relabelClassical S σ) U V
      ∂QAlgorithms.Schur.unitaryHaar d ∂specialUnitaryHaar d = learningDistance hd S := by
    intro σ; rw [← g59c_LD, g59c_LD_rel]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn0 : (0:ℝ) < (Fintype.card (Equiv.Perm (Fin d)) : ℝ) := by exact_mod_cast Fintype.card_pos
  field_simp

theorem g59c_part3 {d N : ℕ} (hd : 0 < d) (S : Branches d N) :
    learningDistance hd (relabelAverage S) ≤ learningDistance hd S :=
  (g59c_stepB hd S).trans (g59c_stepC hd S).le



attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P14.learningMatrixContinuousENorm

/-- PDF p.5, Lemma 4, (28)-(32): classical relabeling average and seed identity.
The undefined M after (28) means N. Odd permutation matrices are implemented
in covariance by a determinant-correcting scalar phase, not by enlarging SU(d). -/
theorem solution {d N : ℕ} (hd : 2 ≤ d) (hN : 1 ≤ N)
    (S : Branches d N) (hS : LearningInstrument 0 S)
    (hdiag : IsDiagonal S) (hcov : IsLearningCovariant S) :
    LearningInstrument 0 (relabelAverage S) ∧ IsLearningSymmetric (relabelAverage S) ∧
    learningDistance (by omega : 0 < d) (relabelAverage S) ≤
      learningDistance (by omega : 0 < d) S ∧
    ∀ sigma : Equiv.Perm (Fin d), ∀ i a b,
      replicatedPOVM (relabelAverage S) 1 (sigma i) (sigma a) (sigma b) =
        replicatedPOVM (relabelAverage S) 1 i a b :=
  ⟨g59c_avg_LI S hS, ⟨g59c_avg_diag S hdiag, g59c_avg_cov S hcov, g59c_avg_inv S⟩, g59c_part3 _ S,
    fun σ i a b => g59c_part4 (by omega) _ (g59c_avg_cov S hcov) (g59c_avg_inv S) σ i a b⟩


end
