-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.symmetries
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:25:09.877438+00:00
-- url     : https://prove2.me/submissions/0b5e43af-817b-4cde-9717-ac93db2414f6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Information100.P37

lemma X7Y_left_entry {ι : Type*} [Fintype ι] [DecidableEq ι] (L X : Matrix ι ι ℂ)
    (s : Equiv.Perm ι) (z : ι → ℂ) (hL : ∀ i j, L i j = if i = s j then z j else 0) (a b : ι) :
    (L * X * Lᴴ) a b = z (s.symm a) * X (s.symm a) (s.symm b) * conj (z (s.symm b)) := by
  have hL' : ∀ i j, L i j = if j = s.symm i then z j else 0 := by
    intro i j; rw [hL]; congr 1; exact propext ⟨fun h => by simp [h], fun h => by simp [h]⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, hL']
  rw [Finset.sum_eq_single (s.symm b)]
  · rw [Finset.sum_eq_single (s.symm a)]
    · simp
    · intro k _ hk; simp [hk]
    · simp
  · intro k _ hk; simp [hk]
  · simp

lemma X7Y_right_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (R : Matrix ι ι ℂ)
    (s : Equiv.Perm ι) (z : ι → ℂ) (hz : ∀ j, Complex.normSq (z j) = 1)
    (hR : ∀ i j, R i j = if i = s j then z j else 0) (p : ι → ℝ) :
    R * inputDensity p * Rᴴ = inputDensity (p ∘ s.symm) := by
  have hR' : ∀ i j, R i j = if j = s.symm i then z j else 0 := by
    intro i j; rw [hR]; congr 1; exact propext ⟨fun h => by simp [h], fun h => by simp [h]⟩
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, hR', inputDensity,
    Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (s.symm b)]
  · rw [Finset.sum_eq_single (s.symm a)]
    · by_cases h : a = b
      · subst h
        simp only [if_true, Function.comp_apply]
        rw [mul_comm (z _), mul_assoc, Complex.mul_conj, hz]; simp
      · have : s.symm a ≠ s.symm b := fun h' => h (s.symm.injective h')
        simp [this, h]
    · intro k _ hk; simp [hk]
    · simp
  · intro k _ hk; simp [hk]
  · simp

lemma X7Y_gen_formula {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    generated (conjSuperop U) = fun p : ι → ℝ => ∑ l, ∑ m, if l = m then 0 else
      Complex.normSq (∑ k, U l k * (p k : ℂ) * conj (U m k)) := by
  funext p
  simp only [generated, coherence]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  congr 1
  simp only [conjSuperop, inputDensity, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

lemma X7Y_gen_meas {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    Measurable (generated (conjSuperop U)) := by
  rw [X7Y_gen_formula]
  apply Continuous.measurable
  refine continuous_finsetSum _ fun l _ => continuous_finsetSum _ fun m _ => ?_
  split_ifs
  · exact continuous_const
  · fun_prop

lemma X7Y_norm_meas {ι : Type*} [Fintype ι] :
    Measurable (normalizePopulation : (ι → ℝ) → (ι → ℝ)) := by
  unfold normalizePopulation
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · fun_prop

lemma X7Y_simplex_perm {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Equiv.Perm ι) :
    (simplexLaw ι).map (fun p => p ∘ s.symm) = simplexLaw ι := by
  have hσ : Measurable (fun p : ι → ℝ => p ∘ s.symm) := by fun_prop
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hpi : (Measure.pi fun _ : ι => expMeasure 1).map (fun p : ι → ℝ => p ∘ s.symm) =
      Measure.pi fun _ : ι => expMeasure 1 := by
    have := (measurePreserving_arrowCongr' (fun _ : ι => expMeasure 1)
      (fun _ : ι => expMeasure 1) s (MeasurableEquiv.refl ℝ)
      (fun _ => MeasurePreserving.id _)).map_eq
    convert this using 2
    funext p i
    simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr']
  have hcomm : (fun p : ι → ℝ => p ∘ s.symm) ∘ normalizePopulation =
      normalizePopulation ∘ (fun p : ι → ℝ => p ∘ s.symm) := by
    funext z
    have hs : ∑ i, z (s.symm i) = ∑ i, z i := Equiv.sum_comp s.symm z
    simp only [Function.comp_apply, normalizePopulation, hs]
    split_ifs <;> rfl
  unfold simplexLaw
  rw [Measure.map_map hσ X7Y_norm_meas, hcomm, ← Measure.map_map X7Y_norm_meas hσ, hpi]

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U L R V : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hL : L ∈ Matrix.unitaryGroup ι ℂ)
    (hR : R ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hLi : IsIncoherent L) (hRi : IsIncoherent R) :
    coherenceLaw (conjSuperop U) = coherenceLaw (conjSuperop (L * U)) ∧
    coherenceLaw (conjSuperop U) = coherenceLaw (conjSuperop (U * R)) ∧
    cgpInBasis V U = cgp (conjSuperop (Vᴴ * U * V)) ∧
    cgpdInBasis V U = cgpd (conjSuperop (Vᴴ * U * V)) := by
  have hbasis : ∀ p, generatedInBasis V U p = generated (conjSuperop (Vᴴ * U * V)) p := by
    intro p
    simp only [generatedInBasis, generated, conjSuperop, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hcgp : cgpInBasis V U = cgp (conjSuperop (Vᴴ * U * V)) := by
    simp only [cgpInBasis, cgp, QAlgorithms.Papers.Independent.Information100.P37.moment, pow_one, hbasis]
  refine ⟨?_, ?_, hcgp, ?_⟩
  · obtain ⟨s, z, hz, hLz⟩ := hLi
    unfold coherenceLaw
    congr 1
    funext p
    simp only [generated, coherence]
    have : conjSuperop (L * U) (inputDensity p) = L * conjSuperop U (inputDensity p) * Lᴴ := by
      simp only [conjSuperop, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this]
    simp only [X7Y_left_entry L _ s z hLz, Complex.normSq_mul, Complex.normSq_conj, hz, one_mul,
      mul_one]
    conv_rhs => rw [← Equiv.sum_comp s]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [← Equiv.sum_comp s]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [s.injective.eq_iff]
  · obtain ⟨s, z, hz, hRz⟩ := hRi
    have hpt : generated (conjSuperop (U * R)) =
        generated (conjSuperop U) ∘ (fun p => p ∘ s.symm) := by
      funext p
      simp only [generated, Function.comp_apply]
      rw [← X7Y_right_diag R s z hz hRz p]
      simp only [conjSuperop, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    unfold coherenceLaw
    rw [hpt, ← Measure.map_map (X7Y_gen_meas U) (by fun_prop), X7Y_simplex_perm]
  · simp only [cgpdInBasis, cgpd, coherenceVariance, hcgp, hbasis]
