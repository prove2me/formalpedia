-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.asymptoticLimit_stabilizable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:15:38.180869+00:00
-- url     : https://prove2.me/submissions/e1999a4d-86d2-4160-8e9e-57c6b20729e7

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P16

lemma X7AL_hull_compact {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  set N := Module.finrank ℝ E + 1
  let Φ : (Fin N → ℝ) × (Fin N → E) → E := fun p => ∑ i, p.1 i • p.2 i
  have hΦ : Continuous Φ := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)
  have hT : IsCompact (stdSimplex ℝ (Fin N) ×ˢ (Set.univ.pi fun _ : Fin N => s)) :=
    IsCompact.prod (isCompact_stdSimplex ℝ (Fin N)) (isCompact_univ_pi fun _ => hs)
  suffices h : convexHull ℝ s = Φ '' (stdSimplex ℝ (Fin N) ×ˢ (Set.univ.pi fun _ : Fin N => s)) by
    rw [h]; exact hT.image hΦ
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨ι, _, z, w, hz, hai, hw0, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard : Fintype.card ι ≤ N := by
      have := hai.card_le_finrank_succ
      have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      omega
    have hne : Nonempty ι := by
      by_contra hem
      rw [not_nonempty_iff] at hem
      simp at hw1
    obtain ⟨i0⟩ := hne
    let e : ι ↪ Fin N := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
    let w' : Fin N → ℝ := Function.extend e w 0
    let z' : Fin N → E := Function.extend e z (fun _ => z i0)
    have hsum : ∀ f : Fin N → E, (∀ j, (¬∃ i, e i = j) → f j = 0) →
        ∑ j, f j = ∑ i, f (e i) := by
      intro f hf
      rw [← Finset.sum_map Finset.univ e f]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      apply hf
      rintro ⟨i, rfl⟩
      exact hj (Finset.mem_map_of_mem _ (Finset.mem_univ _))
    have hsumR : ∀ f : Fin N → ℝ, (∀ j, (¬∃ i, e i = j) → f j = 0) →
        ∑ j, f j = ∑ i, f (e i) := by
      intro f hf
      rw [← Finset.sum_map Finset.univ e f]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      apply hf
      rintro ⟨i, rfl⟩
      exact hj (Finset.mem_map_of_mem _ (Finset.mem_univ _))
    have hw'e : ∀ i, w' (e i) = w i := fun i => e.injective.extend_apply _ _ _
    have hz'e : ∀ i, z' (e i) = z i := fun i => e.injective.extend_apply _ _ _
    have hw'0 : ∀ j, (¬∃ i, e i = j) → w' j = 0 := fun j hj => by
      simp only [w']; rw [Function.extend_apply' _ _ _ hj]; rfl
    refine ⟨(w', z'), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro j
      show 0 ≤ w' j
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj; rw [hw'e]; exact (hw0 i).le
      · rw [hw'0 j hj]
    · show ∑ j, w' j = 1
      rw [hsumR _ hw'0]; simp only [hw'e]; exact hw1
    · intro j _
      show z' j ∈ s
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj; rw [hz'e]; exact hz ⟨i, rfl⟩
      · simp only [z']; rw [Function.extend_apply' _ _ _ hj]; exact hz ⟨i0, rfl⟩
    · show ∑ j, w' j • z' j = x
      rw [hsum (fun j => w' j • z' j) (fun j hj => by simp [hw'0 j hj])]
      simp only [hw'e, hz'e]; exact hx
  · rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (fun i _ => hw.1 i) hw.2
      (fun i _ => subset_convexHull ℝ s (hz i trivial))


lemma X7AL_SU_compact (n : ℕ) :
    IsCompact {U : Matrix (Fin n) (Fin n) ℂ | specialUnitary U} := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  apply hK.of_isClosed_subset
  · have h1 : IsClosed {U : Matrix (Fin n) (Fin n) ℂ | U * star U = 1} :=
      isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
    have h2 : IsClosed {U : Matrix (Fin n) (Fin n) ℂ | U.det = 1} :=
      isClosed_eq (continuous_id.matrix_det) continuous_const
    have : {U : Matrix (Fin n) (Fin n) ℂ | specialUnitary U} =
        {U : Matrix (Fin n) (Fin n) ℂ | U * star U = 1} ∩ {U | U.det = 1} := by
      ext U
      simp [specialUnitary, Matrix.mem_unitaryGroup_iff]
    rw [this]; exact h1.inter h2
  · intro U hU i _ j _
    simpa using entry_norm_bound_of_unitary hU.1 i j

lemma X7AL_rates_cont {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Continuous fun U : Matrix (Fin n) (Fin n) ℂ => rates V U i j := by
  unfold rates
  apply continuous_finsetSum
  intro k _
  exact Complex.continuous_normSq.comp
    (((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id).matrix_elem i j)

lemma X7AL_pg_cont {n r : ℕ} (V : Fin r → Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) :
    Continuous fun U : Matrix (Fin n) (Fin n) ℂ => populationGenerator V U *ᵥ x := by
  apply continuous_pi
  intro i
  simp only [Matrix.mulVec, dotProduct, populationGenerator, Matrix.sub_apply, Matrix.diagonal_apply]
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul _ continuous_const
  apply (X7AL_rates_cont V i j).sub
  split_ifs
  · exact continuous_finsetSum _ fun l _ => X7AL_rates_cont V l _
  · exact continuous_const

lemma X7AL_der_eq {n : ℕ} (D : LindbladData n) (x : Fin n → ℝ) :
    derivatives D x = (fun U => populationGenerator D.jump U *ᵥ x) '' {U | specialUnitary U} := by
  ext v
  simp only [derivatives, fields, Set.mem_image]
  constructor
  · rintro ⟨A, ⟨U, hU, rfl⟩, rfl⟩; exact ⟨U, hU, rfl⟩
  · rintro ⟨U, hU, rfl⟩; exact ⟨_, ⟨U, hU, rfl⟩, rfl⟩

lemma X7AL_hullder_compact {n : ℕ} (D : LindbladData n) (x : Fin n → ℝ) :
    IsCompact (convexHull ℝ (derivatives D x)) := by
  apply X7AL_hull_compact
  rw [X7AL_der_eq]
  exact (X7AL_SU_compact n).image (X7AL_pg_cont D.jump x)


lemma X7AL_iic {n : ℕ} {v : ℝ → Fin n → ℝ} (f : (Fin n → ℝ) →L[ℝ] ℝ) {a b : ℝ}
    (h : IntervalIntegrable v volume a b) : IntervalIntegrable (fun t => f (v t)) volume a b :=
  ⟨f.integrable_comp h.1, f.integrable_comp h.2⟩

lemma X7AL_main {n : ℕ} (D : LindbladData n) (path : ℝ → Fin n → ℝ)
    (hpath : relaxedSolution D (Set.Ici 0) path) (mu : Fin n → ℝ)
    (hlim : Tendsto path atTop (nhds mu)) :
    (0 : Fin n → ℝ) ∈ convexHull ℝ (derivatives D mu) := by
  by_contra h0
  obtain ⟨f, u, w, hfu, huw, hw0⟩ := geometric_hahn_banach_compact_closed (convex_convexHull ℝ _)
    (X7AL_hullder_compact D mu) (convex_singleton (0 : Fin n → ℝ)) isClosed_singleton
    (Set.disjoint_singleton_right.mpr h0)
  have hf0 : f 0 = 0 := map_zero f
  have hu : u < 0 := by have := hw0 0 rfl; rw [hf0] at this; linarith
  set c := -u with hcdef
  have hc : 0 < c := by linarith
  -- uniform bound
  obtain ⟨M, hM⟩ := (X7AL_SU_compact n).exists_bound_of_continuousOn
    (f := fun U => ∑ j, |f (populationGenerator D.jump U *ᵥ Pi.single j 1)|)
    (by
      apply Continuous.continuousOn
      apply continuous_finsetSum
      intro j _
      exact (f.continuous.comp (X7AL_pg_cont D.jump _)).abs)
  have hbound : ∀ U, specialUnitary U → ∀ y : Fin n → ℝ,
      |f (populationGenerator D.jump U *ᵥ y)| ≤ |M| * ∑ j, |y j| := by
    intro U hU y
    have hy : y = ∑ j, y j • (Pi.single j 1 : Fin n → ℝ) := by
      conv_lhs => rw [← Finset.univ_sum_single y]
      congr 1; funext j; ext i; simp [Pi.single_apply]
    have hMU := hM U hU
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at hMU
    calc |f (populationGenerator D.jump U *ᵥ y)|
        = |∑ j, y j * f (populationGenerator D.jump U *ᵥ Pi.single j 1)| := by
          conv_lhs => rw [hy]
          rw [Matrix.mulVec_sum, map_sum]
          simp [Matrix.mulVec_smul]
      _ ≤ ∑ j, |y j| * |f (populationGenerator D.jump U *ᵥ Pi.single j 1)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          simp [abs_mul]
      _ ≤ ∑ j, |y j| * |M| := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine le_trans ?_ (hMU.trans (le_abs_self M))
          exact Finset.single_le_sum (f := fun j => |f (populationGenerator D.jump U *ᵥ Pi.single j 1)|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ = |M| * ∑ j, |y j| := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- closeness
  set δ := c / (2 * (|M| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hcl : Tendsto (fun t => ∑ j, |path t j - mu j|) atTop (nhds 0) := by
    have hcont : Continuous fun y : Fin n → ℝ => ∑ j, |y j - mu j| :=
      continuous_finsetSum _ fun j _ => ((continuous_apply j).sub continuous_const).abs
    have := (hcont.tendsto mu).comp hlim
    simp only [sub_self, abs_zero, Finset.sum_const_zero] at this
    exact this
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp (hcl.eventually (gt_mem_nhds hδ))
  set T1 := max T0 0
  have hpt : ∀ t ≥ T1, ∀ z ∈ convexHull ℝ (derivatives D (path t)), f z ≤ -(c / 2) := by
    intro t ht z hz
    have hsub : derivatives D (path t) ⊆ {z | f z ≤ -(c / 2)} := by
      rintro _ ⟨A, ⟨U, hU, rfl⟩, rfl⟩
      show f (populationGenerator D.jump U *ᵥ path t) ≤ -(c / 2)
      have h1 : f (populationGenerator D.jump U *ᵥ mu) < u :=
        hfu _ (subset_convexHull ℝ _ ⟨_, ⟨U, hU, rfl⟩, rfl⟩)
      have h2 := hbound U hU (path t - mu)
      have h3 : ∑ j, |(path t - mu) j| < δ := hT0 t (le_trans (le_max_left _ _) ht)
      have h4 : |M| * ∑ j, |(path t - mu) j| ≤ c / 2 := by
        have : |M| * ∑ j, |(path t - mu) j| ≤ (|M| + 1) * δ := by
          apply mul_le_mul (by linarith) h3.le (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
        have e : (|M| + 1) * δ = c / 2 := by
          rw [hδdef]; field_simp
        linarith
      have h5 : populationGenerator D.jump U *ᵥ path t =
          populationGenerator D.jump U *ᵥ mu + populationGenerator D.jump U *ᵥ (path t - mu) := by
        rw [← Matrix.mulVec_add]; congr 1; abel
      rw [h5, map_add]
      have := neg_abs_le (f (populationGenerator D.jump U *ᵥ (path t - mu)))
      have := le_abs_self (f (populationGenerator D.jump U *ᵥ (path t - mu)))
      linarith
    exact convexHull_min hsub (convex_halfSpace_le f.toLinearMap.isLinear _) hz
  obtain ⟨hsimp, v, hint, hae⟩ := hpath
  have hrep : ∀ t ≥ 0, f (path t) = f (path 0) + ∫ s in (0 : ℝ)..t, f (v s) := by
    intro t ht
    obtain ⟨hi, he⟩ := hint t ht
    rw [he, map_add, ContinuousLinearMap.intervalIntegral_comp_comm f hi]
  have hgrow : ∀ t ≥ T1, f (path t) ≤ f (path T1) - (c / 2) * (t - T1) := by
    intro t ht
    have hT1 : (0 : ℝ) ≤ T1 := le_max_right _ _
    have ht0 : (0 : ℝ) ≤ t := le_trans hT1 ht
    rw [hrep t ht0, hrep T1 hT1]
    have hi1 := X7AL_iic f (hint t ht0).1
    have hi2 := X7AL_iic f (hint T1 hT1).1
    have hsub := intervalIntegral.integral_interval_sub_left hi1 hi2
    have hmono : (∫ s in T1..t, f (v s)) ≤ ∫ s in T1..t, (-(c / 2) : ℝ) := by
      apply intervalIntegral.integral_mono_ae_restrict ht
        ((hi2.symm.trans hi1)) intervalIntegrable_const
      have hae' : ∀ᵐ s ∂(volume.restrict (Set.Icc T1 t)), v s ∈ convexHull ℝ (derivatives D (path s)) :=
        ae_restrict_of_ae_restrict_of_subset (fun s hs => le_trans hT1 hs.1) hae
      filter_upwards [hae', ae_restrict_mem measurableSet_Icc] with s hs hsI
      exact hpt s hsI.1 _ hs
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith
  have hfl : Tendsto (fun t => f (path t)) atTop (nhds (f mu)) := (f.continuous.tendsto mu).comp hlim
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp (hfl.eventually (lt_mem_nhds (show f mu - 1 < f mu by linarith)))
  set t := max T1 T2 + 2 * (|f (path T1) - f mu| + 1) / c
  have hpos : 0 ≤ 2 * (|f (path T1) - f mu| + 1) / c := by positivity
  have ht1 : T1 ≤ t := le_trans (le_max_left _ _) (le_add_of_nonneg_right hpos)
  have ht2 : T2 ≤ t := le_trans (le_max_right _ _) (le_add_of_nonneg_right hpos)
  have e1 := hgrow t ht1
  have e2 := hT2 t ht2
  have e3 : (c / 2) * (t - T1) ≥ |f (path T1) - f mu| + 1 := by
    have : t - T1 ≥ 2 * (|f (path T1) - f mu| + 1) / c := by
      have := le_max_left T1 T2; simp only [t]; linarith
    calc (c / 2) * (t - T1) ≥ (c / 2) * (2 * (|f (path T1) - f mu| + 1) / c) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = |f (path T1) - f mu| + 1 := by field_simp
  have e4 := le_abs_self (f (path T1) - f mu)
  linarith

end QAlgorithms.Papers.Independent.Dependency50.P16

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Dependency50.P16 in
theorem solution {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (path : ℝ → (fun n : ℕ => Fin n → ℝ) n) (hpath : relaxedSolution D (Set.Ici 0) path)
    (mu : (fun n : ℕ => Fin n → ℝ) n) (hmu : mu ∈ simplex n) (hlim : Tendsto path atTop (nhds mu)) :
    stabilizable D mu :=
  ⟨hmu, X7AL_main D path hpath mu hlim⟩
