-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.fourCopyRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:39:01.385272+00:00
-- url     : https://prove2.me/submissions/ac11ea3c-49ec-4c02-9360-7f42185c5dc9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped BigOperators Matrix ComplexConjugate Topology ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P37

instance X7S_probExp : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

lemma X7S_exp_pos : ∀ᵐ x ∂(expMeasure 1), (0:ℝ) < x := by
  have hf : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, ae_withDensity_iff hf]
  have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [hne] with x hx hpdf
  rcases lt_or_gt_of_ne hx with h | h
  · exact absurd (gammaPDF_of_neg h) hpdf
  · exact h

lemma X7S_pi_pos {ι : Type*} [Fintype ι] :
    ∀ᵐ z ∂(Measure.pi fun _ : ι => expMeasure 1), ∀ i, (0:ℝ) < z i :=
  eventually_all.2 fun _ => Measure.tendsto_eval_ae_ae.eventually X7S_exp_pos

lemma X7S_norm_meas {ι : Type*} [Fintype ι] :
    Measurable (normalizePopulation : (ι → ℝ) → (ι → ℝ)) := by
  unfold normalizePopulation
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · fun_prop

instance X7S_prob {ι : Type*} [Fintype ι] : IsProbabilityMeasure (simplexLaw ι) := by
  unfold simplexLaw
  exact Measure.isProbabilityMeasure_map X7S_norm_meas.aemeasurable

lemma X7S_ae_simplex {ι : Type*} [Fintype ι] :
    ∀ᵐ p ∂(simplexLaw ι), p ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1) := by
  unfold simplexLaw
  have hs : MeasurableSet {y : ι → ℝ | y ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1)} :=
    (isClosed_set_pi fun _ _ => isClosed_Icc).measurableSet
  refine (ae_map_iff X7S_norm_meas.aemeasurable hs).mpr ?_
  filter_upwards [X7S_pi_pos] with z hz
  intro i _
  have hcard : (1:ℝ) ≤ Fintype.card ι := by
    have := Fintype.card_pos_iff.mpr ⟨i⟩; exact_mod_cast this
  unfold normalizePopulation
  split_ifs with h0
  · exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact hcard⟩
  · have hS : 0 < ∑ j, z j := Finset.sum_pos (fun j _ => hz j) ⟨i, Finset.mem_univ i⟩
    refine ⟨div_nonneg (hz i).le hS.le, (div_le_one hS).mpr ?_⟩
    exact Finset.single_le_sum (fun j _ => (hz j).le) (Finset.mem_univ i)

lemma X7F_int {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] (f : (ι → ℝ) → E) (hf : Continuous f) :
    Integrable f (simplexLaw ι) := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ : ι => isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [X7S_ae_simplex] with p hp
  exact hC p hp

lemma X7F_kmul {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) (A B : Matrix α α ℂ) :
    piKron n A * piKron n B = piKron n (A * B) := by
  ext x z
  simp only [piKron, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun y => ?_
  rw [Finset.prod_mul_distrib]

lemma X7F_kconj {α : Type*} [Fintype α] (n : ℕ) (A : Matrix α α ℂ) :
    (piKron n A)ᴴ = piKron n Aᴴ := by
  ext x z
  simp [piKron, Matrix.conjTranspose_apply, map_prod]

lemma X7F_T {α : Type*} [Fintype α] [DecidableEq α] (σ : Matrix α α ℂ) :
    (coherenceObservable α * Matrix.kronecker σ σ).trace =
      ∑ i, ∑ j, σ j i * σ i j - ∑ i, σ i i * σ i i := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, coherenceObservable, sub_mul,
    Finset.sum_sub_distrib, Matrix.kronecker_apply, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro b _ hb; rw [Finset.sum_eq_zero]; intro c _; simp [hb]; intro _ h; exact absurd h.symm hb
    · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
      · simp [Matrix.kronecker_apply]
      · intro b _ hb; simp [Ne.symm hb]
      · simp
      · intro b _ hb; apply Finset.sum_eq_zero; intro c _; simp [Ne.symm hb]
      · simp
    · intro b _ hb; apply Finset.sum_eq_zero; intro c _; apply Finset.sum_eq_zero; intro e _
      simp [Ne.symm hb]
    · simp

lemma X7F_herm {α : Type*} [Fintype α] [DecidableEq α] (σ : Matrix α α ℂ) (hσ : σ.IsHermitian) :
    (coherenceObservable α * Matrix.kronecker σ σ).trace = (coherence σ : ℂ) := by
  have hji : ∀ i j, σ j i = conj (σ i j) := fun i j => by
    rw [← hσ.apply j i]; rfl
  rw [X7F_T]
  have e1 : ∀ i j, σ j i * σ i j = (Complex.normSq (σ i j) : ℂ) := fun i j => by
    rw [hji, Complex.normSq_eq_conj_mul_self]
  have e2 : ∀ i, σ i i * σ i i = (Complex.normSq (σ i i) : ℂ) := fun i => by
    have := e1 i i; exact this
  simp only [e1, e2, coherence]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (∑ j, ((if i = j then (0:ℝ) else Complex.normSq (σ i j) : ℝ) : ℂ)) =
      ∑ j, ((Complex.normSq (σ i j) : ℂ) - if i = j then (Complex.normSq (σ i j) : ℂ) else 0) from
    Finset.sum_congr rfl fun j _ => by split_ifs <;> simp]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

def X7F_e (α : Type*) : (Fin 4 → α) ≃ (α × α) × (α × α) where
  toFun a := ((a 0, a 1), (a 2, a 3))
  invFun x := ![x.1.1, x.1.2, x.2.1, x.2.2]
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv x := rfl

lemma X7F_four (d : ℕ) (σ : Matrix (Fin d) (Fin d) ℂ) :
    (fourCopyObservable d * piKron 4 σ).trace =
      ((coherenceObservable (Fin d) * Matrix.kronecker σ σ).trace) ^ 2 := by
  set g : (Fin d × Fin d) → (Fin d × Fin d) → ℂ :=
    fun x y => coherenceObservable (Fin d) x y * (σ y.1 x.1 * σ y.2 x.2) with hg
  have hT : (coherenceObservable (Fin d) * Matrix.kronecker σ σ).trace = ∑ x, ∑ y, g x y := by
    simp [Matrix.trace, Matrix.mul_apply, g, Matrix.kronecker_apply]
  have he : ∀ a : Fin 4 → Fin d, X7F_e (Fin d) a = ((a 0, a 1), (a 2, a 3)) := fun _ => rfl
  have hL : (fourCopyObservable d * piKron 4 σ).trace =
      ∑ a, ∑ b, g (X7F_e _ a).1 (X7F_e _ b).1 * g (X7F_e _ a).2 (X7F_e _ b).2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, fourCopyObservable, piKron,
      Matrix.of_apply, Fin.prod_univ_four, g, he]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hL' : (fourCopyObservable d * piKron 4 σ).trace = ∑ X : (Fin d × Fin d) × (Fin d × Fin d), ∑ Y : (Fin d × Fin d) × (Fin d × Fin d), g X.1 Y.1 * g X.2 Y.2 := by
    rw [hL, ← (X7F_e (Fin d)).sum_comp (fun X : (Fin d × Fin d) × (Fin d × Fin d) => ∑ Y : (Fin d × Fin d) × (Fin d × Fin d), g X.1 Y.1 * g X.2 Y.2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact ((X7F_e (Fin d)).sum_comp (fun Y : (Fin d × Fin d) × (Fin d × Fin d) => g (X7F_e _ a).1 Y.1 * g (X7F_e _ a).2 Y.2))
  rw [hL', hT, sq, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum, Fintype.sum_prod_type]

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution (d : ℕ) (hd : 1 ≤ d) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (∀ s : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix s →
      coherence s = ((coherenceObservable (Fin d) * Matrix.kronecker s s).trace).re) ∧
    Papers.Independent.Information100.P37.moment (conjSuperop U) 2 =
      ((fourCopyObservable d * piKron 4 U * momentState d 4 * (piKron 4 U)ᴴ).trace).re := by
  refine ⟨fun s hs => by rw [X7F_herm s hs.1.isHermitian]; simp, ?_⟩
  set σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℂ := fun p => conjSuperop U (inputDensity p) with hσ
  have hσH : ∀ p, (σ p).IsHermitian := fun p => by
    refine Matrix.isHermitian_mul_mul_conjTranspose U ?_
    refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
    funext i; simp [Complex.conj_ofReal]
  have hint : ∀ a b : Fin 4 → Fin d,
      Integrable (fun p => piKron 4 (inputDensity p) a b) (simplexLaw (Fin d)) := by
    intro a b
    refine X7F_int _ ?_
    simp only [piKron, Matrix.of_apply, inputDensity, Matrix.diagonal_apply]
    exact continuous_finsetProd _ fun i _ => by split_ifs <;> fun_prop
  have hexp : ∀ p a c, piKron 4 (σ p) a c =
      ∑ b', (∑ b, piKron 4 U a b * piKron 4 (inputDensity p) b b') * (piKron 4 U)ᴴ b' c := by
    intro p a c
    simp only [σ, conjSuperop, ← X7F_kmul, X7F_kconj, Matrix.mul_apply]
  have hint2 : ∀ a c : Fin 4 → Fin d,
      Integrable (fun p => piKron 4 (σ p) a c) (simplexLaw (Fin d)) := by
    intro a c
    simp_rw [hexp]
    exact integrable_finsetSum _ fun b' _ =>
      (integrable_finsetSum _ fun b _ => (hint b b').const_mul _).mul_const _
  have hmid : piKron 4 U * (momentState d 4 * (piKron 4 U)ᴴ) =
      Matrix.of fun a c => ∫ p, piKron 4 (σ p) a c ∂simplexLaw (Fin d) := by
    ext a c
    rw [Matrix.of_apply]
    simp_rw [hexp]
    rw [← Matrix.mul_assoc]
    simp only [Matrix.mul_apply, momentState]
    rw [integral_finsetSum _ (fun b' _ =>
      ((integrable_finsetSum _ fun b _ => (hint b b').const_mul _).mul_const _))]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [integral_mul_const, integral_finsetSum _ fun b _ => (hint b b').const_mul _]
    congr 1
    exact Finset.sum_congr rfl fun b _ => (integral_const_mul _ _).symm
  simp only [Matrix.mul_assoc]
  rw [hmid]
  have htr : (fourCopyObservable d * Matrix.of fun a c => ∫ p, piKron 4 (σ p) a c ∂simplexLaw (Fin d)).trace =
      ∫ p, (fourCopyObservable d * piKron 4 (σ p)).trace ∂simplexLaw (Fin d) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
    symm
    rw [integral_finsetSum _ (fun a _ => ?_)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ (fun c _ => ?_)]
      · exact Finset.sum_congr rfl fun c _ => integral_const_mul _ _
      · exact (hint2 c a).const_mul _
    · exact integrable_finsetSum _ fun c _ => (hint2 c a).const_mul _
  rw [htr]
  have hpt : ∀ p, (fourCopyObservable d * piKron 4 (σ p)).trace =
      ((generated (conjSuperop U) p ^ 2 : ℝ) : ℂ) := by
    intro p
    rw [X7F_four, X7F_herm _ (hσH p)]
    push_cast; rfl
  simp_rw [hpt]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  rfl
