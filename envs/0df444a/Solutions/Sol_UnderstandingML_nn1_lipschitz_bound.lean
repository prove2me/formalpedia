-- Prove2me | solution 1 for UnderstandingML.nn1_lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T07:43:33.422987+00:00
-- url     : https://prove2.me/submissions/aeeae22e-0d12-45d9-8636-a34cf2765de9

import Definitions.Def_UnderstandingML_NearestNeighbor
import Mathlib

open MeasureTheory

namespace NNInfra

open UnderstandingML

section General

variable {X : Type*}

/-- Weight of label `b` at `x`: `η x` for `true`, `1 - η x` for `false`. -/
def wt (η : X → ℝ) (x : X) (b : Bool) : ℝ := if b then η x else 1 - η x

lemma wt_nonneg {η : X → ℝ} (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (x : X) (b : Bool) :
    0 ≤ wt η x b := by
  have := hη01 x; cases b <;> simp [wt] <;> linarith [this.1, this.2]

lemma wt_le_one {η : X → ℝ} (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (x : X) (b : Bool) :
    wt η x b ≤ 1 := by
  have := hη01 x; cases b <;> simp [wt] <;> linarith [this.1, this.2]

lemma wt_sum (η : X → ℝ) (x : X) : wt η x true + wt η x false = 1 := by simp [wt]

variable [MeasurableSpace X]

lemma measurable_wt {η : X → ℝ} (hη : Measurable η) (b : Bool) : Measurable (fun x ↦ wt η x b) := by
  cases b
  · exact measurable_const.sub hη
  · exact hη

lemma bernoulliLaw_apply (p : ℝ) (A : Set Bool) :
    bernoulliLaw p A = ENNReal.ofReal p * A.indicator 1 true +
      ENNReal.ofReal (1 - p) * A.indicator 1 false := by
  simp [bernoulliLaw, Measure.dirac_apply' _ (MeasurableSet.of_discrete : MeasurableSet A)]

lemma kernel_apply (η : X → ℝ) {s : Set (X × Bool)} (hs : MeasurableSet s) (x : X) :
    ((bernoulliLaw (η x)).map (fun y ↦ (x, y))) s =
      ∑ b : Bool, {x | (x, b) ∈ s}.indicator (fun x ↦ ENNReal.ofReal (wt η x b)) x := by
  rw [Measure.map_apply measurable_prodMk_left hs, bernoulliLaw_apply]
  simp [Set.indicator, wt, add_comm]; rfl

lemma kernel_measurable {η : X → ℝ} (hη : Measurable η) :
    Measurable (fun x ↦ (bernoulliLaw (η x)).map (fun y ↦ (x, y))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [kernel_apply η hs]
  exact Finset.measurable_sum _ (fun b _ ↦ ((ENNReal.measurable_ofReal.comp
    (measurable_wt hη b))).indicator (measurable_prodMk_right hs))

lemma condLaw_apply {DX : Measure X} {η : X → ℝ} (hη : Measurable η) {s : Set (X × Bool)}
    (hs : MeasurableSet s) :
    condLaw DX η s = ∑ b : Bool, ∫⁻ x in {x | (x, b) ∈ s}, ENNReal.ofReal (wt η x b) ∂DX := by
  rw [condLaw, Measure.bind_apply hs (kernel_measurable hη).aemeasurable]
  simp_rw [kernel_apply η hs]
  rw [lintegral_finsetSum]
  · congr 1; funext b
    exact lintegral_indicator (measurable_prodMk_right hs) _
  · intro b _
    exact (ENNReal.measurable_ofReal.comp (measurable_wt hη b)).indicator
      (measurable_prodMk_right hs)

lemma condLaw_isProb {DX : Measure X} [IsProbabilityMeasure DX] {η : X → ℝ} (hη : Measurable η)
    (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (condLaw DX η) := by
  constructor
  rw [condLaw_apply hη MeasurableSet.univ]
  simp only [Set.mem_univ, Set.ofPred_true, Measure.restrict_univ]
  rw [← lintegral_finsetSum (μ := DX) Finset.univ (f := fun b x ↦ ENNReal.ofReal (wt η x b))
    (fun b _ ↦ ENNReal.measurable_ofReal.comp (measurable_wt hη b))]
  have : ∀ x, ∑ b : Bool, ENNReal.ofReal (wt η x b) = 1 := by
    intro x
    rw [Fintype.sum_bool, ← ENNReal.ofReal_add (wt_nonneg hη01 x true) (wt_nonneg hη01 x false),
      wt_sum]; simp
  rw [lintegral_congr (fun x ↦ this x)]; simp

/-- the product of lintegrals formula for bounded nonnegative real functions -/
lemma lintegral_pi_prod {ι : Type*} [Fintype ι] (μ : ι → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i)) (h0 : ∀ i x, 0 ≤ f i x)
    (h1 : ∀ i x, f i x ≤ 1) :
    ∫⁻ xs, ∏ i, ENNReal.ofReal (f i (xs i)) ∂(Measure.pi μ) =
      ∏ i, ∫⁻ x, ENNReal.ofReal (f i x) ∂(μ i) := by
  have hint : ∀ i, Integrable (f i) (μ i) := fun i ↦
    Integrable.of_bound (hf i).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 i x)]; exact h1 i x))
  have hprod_int : Integrable (fun xs : ι → X ↦ ∏ i, f i (xs i)) (Measure.pi μ) := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall (fun xs ↦ ?_))
    · exact (Finset.measurable_prod _ (fun i _ ↦ (hf i).comp (measurable_pi_apply i))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i _ ↦ h0 i _))]
      exact Finset.prod_le_one (fun i _ ↦ h0 i _) (fun i _ ↦ h1 i _)
  simp_rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ h0 i _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hprod_int
    (Filter.Eventually.of_forall (fun xs ↦ Finset.prod_nonneg (fun i _ ↦ h0 i _))),
    integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun i x ↦ f i x),
    ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ integral_nonneg (h0 i))]
  congr 1; funext i
  exact ofReal_integral_eq_lintegral_ofReal (hint i) (Filter.Eventually.of_forall (h0 i))

/-- attach labels `ys` to instances `xs` -/
def zipL {m : ℕ} (ys : Fin m → Bool) (xs : Fin m → X) : Fin m → X × Bool := fun i ↦ (xs i, ys i)

lemma measurableEmbedding_zipL {m : ℕ} (ys : Fin m → Bool) :
    MeasurableEmbedding (zipL (X := X) ys) := by
  refine MeasurableEmbedding.of_measurable_inverse (g := fun S i ↦ (S i).1) ?_ ?_ ?_ ?_
  · exact measurable_pi_lambda _ (fun i ↦ (measurable_pi_apply i).prodMk measurable_const)
  · have : Set.range (zipL (X := X) ys) = ⋂ i, {S | (S i).2 = ys i} := by
      ext S; simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨xs, rfl⟩ i; rfl
      · intro h; exact ⟨fun i ↦ (S i).1, funext fun i ↦ Prod.ext rfl (h i).symm⟩
    rw [this]
    exact MeasurableSet.iInter (fun i ↦ (measurable_snd.comp (measurable_pi_apply i))
      (MeasurableSet.singleton _))
  · exact measurable_pi_lambda _ (fun i ↦ measurable_fst.comp (measurable_pi_apply i))
  · intro xs; rfl

/-- density of the label vector `ys` given the instances -/
noncomputable def dens {m : ℕ} (η : X → ℝ) (ys : Fin m → Bool) (xs : Fin m → X) : NNReal :=
  ∏ i, (wt η (xs i) (ys i)).toNNReal

lemma measurable_dens {m : ℕ} {η : X → ℝ} (hη : Measurable η) (ys : Fin m → Bool) :
    Measurable (dens η ys) :=
  Finset.measurable_prod _ (fun i _ ↦ ((measurable_wt hη (ys i)).comp
    (measurable_pi_apply i)).real_toNNReal)

omit [MeasurableSpace X] in
lemma dens_coe {m : ℕ} {η : X → ℝ} (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (ys : Fin m → Bool)
    (xs : Fin m → X) : (dens η ys xs : ℝ) = ∏ i, wt η (xs i) (ys i) := by
  simp [dens, Real.coe_toNNReal _ (wt_nonneg hη01 _ _)]

variable {DX : Measure X} [IsProbabilityMeasure DX] {η : X → ℝ}

lemma iid_condLaw_eq (hη : Measurable η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) :
    iidLaw (condLaw DX η) m = ∑ ys : Fin m → Bool,
      ((iidLaw DX m).withDensity (fun xs ↦ (dens η ys xs : ENNReal))).map (zipL ys) := by
  have := condLaw_isProb (DX := DX) hη hη01
  unfold iidLaw
  apply Measure.pi_eq
  intro s hs
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have hpre : ∀ ys : Fin m → Bool, zipL ys ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i ↦ {x | (x, ys i) ∈ s i}) := by
    intro ys; ext xs; simp [zipL]
  have hmeas : ∀ ys : Fin m → Bool, MeasurableSet (Set.univ.pi (fun i ↦ {x : X | (x, ys i) ∈ s i})) :=
    fun ys ↦ MeasurableSet.univ_pi (fun i ↦ measurable_prodMk_right (hs i))
  have hterm : ∀ ys : Fin m → Bool,
      ((Measure.pi (fun _ : Fin m ↦ DX)).withDensity (fun xs ↦ (dens η ys xs : ENNReal))).map
        (zipL ys) (Set.univ.pi s) =
      ∏ i, ∫⁻ x in {x | (x, ys i) ∈ s i}, ENNReal.ofReal (wt η x (ys i)) ∂DX := by
    intro ys
    rw [Measure.map_apply (measurableEmbedding_zipL ys).measurable (MeasurableSet.univ_pi hs),
      hpre, withDensity_apply _ (hmeas ys), Measure.restrict_pi_pi]
    have : (fun xs : Fin m → X ↦ (dens η ys xs : ENNReal)) =
        fun xs ↦ ∏ i, ENNReal.ofReal (wt η (xs i) (ys i)) := by
      funext xs; simp [dens, ENNReal.ofReal]
    rw [this]
    exact lintegral_pi_prod _ (fun i x ↦ wt η x (ys i)) (fun i ↦ measurable_wt hη _)
      (fun i x ↦ wt_nonneg hη01 x _) (fun i x ↦ wt_le_one hη01 x _)
  simp_rw [hterm]
  classical
  rw [← Fintype.prod_sum
    (fun i b ↦ ∫⁻ x in {x | (x, b) ∈ s i}, ENNReal.ofReal (wt η x b) ∂DX)]
  congr 1; funext i
  rw [condLaw_apply hη (hs i)]

lemma iid_isProb (D : Measure X) [IsProbabilityMeasure D] (m : ℕ) :
    IsProbabilityMeasure (iidLaw D m) := by
  unfold iidLaw; infer_instance

/-- **Label decomposition.** The expectation over a labeled i.i.d. sample equals the expectation
over the unlabeled sample of the finite average over label vectors. -/
lemma integral_iid_condLaw (hη : Measurable η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (m : ℕ)
    (F : (Fin m → X × Bool) → ℝ) (hF : Integrable F (iidLaw (condLaw DX η) m)) :
    ∫ S, F S ∂(iidLaw (condLaw DX η) m) =
      ∫ xs, ∑ ys : Fin m → Bool, (∏ i, wt η (xs i) (ys i)) * F (zipL ys xs) ∂(iidLaw DX m) := by
  have hle : ∀ ys : Fin m → Bool,
      ((iidLaw DX m).withDensity (fun xs ↦ (dens η ys xs : ENNReal))).map (zipL ys) ≤
        iidLaw (condLaw DX η) m := by
    intro ys
    rw [iid_condLaw_eq hη hη01 m]
    exact Finset.single_le_sum (f := fun ys ↦
      ((iidLaw DX m).withDensity (fun xs ↦ (dens η ys xs : ENNReal))).map (zipL ys))
      (fun _ _ ↦ Measure.zero_le _) (Finset.mem_univ ys)
  have hint : ∀ ys : Fin m → Bool, Integrable (fun xs ↦ (dens η ys xs) • F (zipL ys xs))
      (iidLaw DX m) := by
    intro ys
    have h1 := (hF.mono_measure (hle ys))
    rw [(measurableEmbedding_zipL ys).integrable_map_iff,
      integrable_withDensity_iff_integrable_smul (measurable_dens hη ys)] at h1
    exact h1
  rw [iid_condLaw_eq hη hη01 m, integral_finsetSum_measure (fun ys _ ↦ hF.mono_measure (hle ys))]
  rw [integral_finsetSum _ (fun ys _ ↦ by
    have := hint ys
    refine this.congr (Filter.Eventually.of_forall (fun xs ↦ ?_))
    simp [NNReal.smul_def, dens_coe hη01])]
  congr 1; funext ys
  rw [(measurableEmbedding_zipL ys).integral_map,
    integral_withDensity_eq_integral_smul (measurable_dens hη ys)]
  congr 1; funext xs
  simp [NNReal.smul_def, dens_coe hη01]

lemma integrable_decomp (hη : Measurable η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) (m : ℕ)
    (F : (Fin m → X × Bool) → ℝ) (hF : Integrable F (iidLaw (condLaw DX η) m)) :
    Integrable (fun xs ↦ ∑ ys : Fin m → Bool, (∏ i, wt η (xs i) (ys i)) * F (zipL ys xs))
      (iidLaw DX m) := by
  have hle : ∀ ys : Fin m → Bool,
      ((iidLaw DX m).withDensity (fun xs ↦ (dens η ys xs : ENNReal))).map (zipL ys) ≤
        iidLaw (condLaw DX η) m := by
    intro ys
    rw [iid_condLaw_eq hη hη01 m]
    exact Finset.single_le_sum (f := fun ys ↦
      ((iidLaw DX m).withDensity (fun xs ↦ (dens η ys xs : ENNReal))).map (zipL ys))
      (fun _ _ ↦ Measure.zero_le _) (Finset.mem_univ ys)
  refine integrable_finsetSum _ (fun ys _ ↦ ?_)
  have h1 := (hF.mono_measure (hle ys))
  rw [(measurableEmbedding_zipL ys).integrable_map_iff,
    integrable_withDensity_iff_integrable_smul (measurable_dens hη ys)] at h1
  refine h1.congr (Filter.Eventually.of_forall (fun xs ↦ ?_))
  simp [NNReal.smul_def, dens_coe hη01]

/-- **Single-point label decomposition.** -/
lemma integral_condLaw (hη : Measurable η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (G : X × Bool → ℝ) (hG : Integrable G (condLaw DX η)) :
    ∫ z, G z ∂(condLaw DX η) = ∫ x, ∑ b : Bool, wt η x b * G (x, b) ∂DX := by
  have := condLaw_isProb (DX := DX) hη hη01
  have e1 := (measurePreserving_funUnique (condLaw DX η) (Fin 1))
  have e2 := (measurePreserving_funUnique DX (Fin 1))
  have hF : Integrable (fun S : Fin 1 → X × Bool ↦ G (S 0)) (iidLaw (condLaw DX η) 1) := by
    have := (e1.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hG
    exact this
  have h1 : ∫ z, G z ∂(condLaw DX η) = ∫ S, G (S 0) ∂(iidLaw (condLaw DX η) 1) := by
    rw [iidLaw, ← e1.integral_comp (MeasurableEquiv.measurableEmbedding _)]; rfl
  have h2 : ∫ x, ∑ b : Bool, wt η x b * G (x, b) ∂DX =
      ∫ xs, ∑ b : Bool, wt η (xs 0) b * G (xs 0, b) ∂(iidLaw DX 1) := by
    rw [iidLaw, ← e2.integral_comp (MeasurableEquiv.measurableEmbedding _)]; rfl
  rw [h1, h2, integral_iid_condLaw hη hη01 1 _ hF]
  congr 1; funext xs
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp [zipL]

lemma measurable_loss01 {h' : X → Bool} (hh' : Measurable h') :
    Measurable (loss01 h' : X × Bool → ℝ) := by
  unfold loss01
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_eq_fun (hh'.comp measurable_fst) measurable_snd

lemma risk_condLaw (hη : Measurable η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    {h' : X → Bool} (hh' : Measurable h') :
    risk loss01 (condLaw DX η) h' = ∫ x, bernoulliErr (η x) (h' x) ∂DX := by
  have := condLaw_isProb (DX := DX) hη hη01
  rw [risk, integral_condLaw hη hη01]
  · congr 1; funext x
    cases hx : h' x <;> simp [wt, loss01, bernoulliErr, hx]
  · refine Integrable.of_bound (measurable_loss01 hh').aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z ↦ ?_))
    unfold loss01; split_ifs <;> simp

end General

/-- marginalization of a product weight over all label vectors -/
lemma sum_prod_marginal {m : ℕ} (w : Fin m → Bool → ℝ) (hw : ∀ i, w i true + w i false = 1)
    (j : Fin m) (φ : Bool → ℝ) :
    ∑ ys : Fin m → Bool, (∏ i, w i (ys i)) * φ (ys j) = w j true * φ true + w j false * φ false := by
  classical
  have h1 : ∀ ys : Fin m → Bool, (∏ i, w i (ys i)) * φ (ys j) =
      ∏ i, (w i (ys i) * (if i = j then φ (ys i) else 1)) := by
    intro ys
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j (fun i ↦ φ (ys i))]
    simp
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i b ↦ w i b * (if i = j then φ b else 1))]
  have h2 : ∀ i, ∑ b : Bool, w i b * (if i = j then φ b else 1) =
      if i = j then w j true * φ true + w j false * φ false else 1 := by
    intro i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, hw i]
  simp_rw [h2]
  rw [Finset.prod_ite_eq' Finset.univ j]
  simp

lemma sum_prod_one {m : ℕ} (w : Fin m → Bool → ℝ) (hw : ∀ i, w i true + w i false = 1) :
    ∑ ys : Fin m → Bool, (∏ i, w i (ys i)) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun i b ↦ w i b)]
  simp [hw]

lemma cube_dist_le {d : ℕ} (x y : cube d) : dist x y ≤ Real.sqrt d := by
  rw [Subtype.dist_eq, EuclideanSpace.dist_eq]
  apply Real.sqrt_le_sqrt
  have : ∀ i, dist (x.1.ofLp i) (y.1.ofLp i) ^ 2 ≤ 1 := by
    intro i
    have hx := x.2 i; have hy := y.2 i
    rw [Real.dist_eq, sq_abs]
    simp only [Set.mem_Icc] at hx hy
    nlinarith
  calc ∑ i, dist (x.1.ofLp i) (y.1.ofLp i) ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ ↦ this i)
    _ = d := by simp

lemma measurable_nnDist {d m : ℕ} :
    Measurable (fun p : (Fin m → cube d × Bool) × cube d ↦ nnDist p.1 p.2) := by
  unfold nnDist
  refine Measurable.iInf (fun i ↦ ?_)
  exact (continuous_snd.dist ((continuous_apply i).comp continuous_fst).fst).measurable

lemma nnDist_nonneg {d m : ℕ} (S : Fin m → cube d × Bool) (x : cube d) : 0 ≤ nnDist S x := by
  unfold nnDist
  rcases isEmpty_or_nonempty (Fin m) with h | h
  · simp [Real.iInf_of_isEmpty]
  · exact le_ciInf (fun i ↦ dist_nonneg)

lemma nnDist_le {d m : ℕ} (S : Fin m → cube d × Bool) (x : cube d) : nnDist S x ≤ Real.sqrt d := by
  unfold nnDist
  rcases isEmpty_or_nonempty (Fin m) with h | ⟨⟨i⟩⟩
  · simp [Real.iInf_of_isEmpty]
  · exact le_trans (ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact dist_nonneg⟩ i) (cube_dist_le _ _)

end NNInfra

open UnderstandingML NNInfra in
theorem solution (d : ℕ) (DX : Measure (cube d)) [IsProbabilityMeasure DX]
    (η : cube d → ℝ) (c : NNReal) (hη : LipschitzWith c η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (h : Learner (cube d × Bool) (cube d → Bool)) (hnn : IsNN1Rule h)
    (hmeas : ∀ m, Measurable (fun p : (Fin m → cube d × Bool) × cube d ↦ h m p.1 p.2))
    (m : ℕ) (hm : 0 < m) :
    ∫ S, risk loss01 (condLaw DX η) (h m S) ∂(iidLaw (condLaw DX η) m) ≤
      2 * risk loss01 (condLaw DX η) (bayesRule η) +
        c * ∫ p, nnDist p.1 p.2 ∂((iidLaw (condLaw DX η) m).prod DX) := by
  classical
  obtain ⟨π, hsort, hrule⟩ := hnn
  have hηm : Measurable η := hη.continuous.measurable
  have hD := condLaw_isProb (DX := DX) hηm hη01
  have hI := iid_isProb (condLaw DX η) m
  have hIX := iid_isProb DX m
  set I := iidLaw (condLaw DX η) m with hIdef
  let Φ : (Fin m → cube d × Bool) → cube d → ℝ := fun S x ↦ bernoulliErr (η x) (h m S x)
  have hΦm : Measurable (Function.uncurry Φ) := by
    have hset : MeasurableSet {p : (Fin m → cube d × Bool) × cube d | h m p.1 p.2 = true} :=
      (hmeas m) (MeasurableSet.singleton true)
    change Measurable (fun p : (Fin m → cube d × Bool) × cube d ↦
      bernoulliErr (η p.2) (h m p.1 p.2))
    unfold bernoulliErr
    exact Measurable.ite hset (measurable_const.sub (hηm.comp measurable_snd))
      (hηm.comp measurable_snd)
  have hΦb : ∀ S x, 0 ≤ Φ S x ∧ Φ S x ≤ 1 := by
    intro S x
    have := hη01 x
    simp only [Φ, bernoulliErr]
    split_ifs <;> constructor <;> linarith [this.1, this.2]
  have hΦint : Integrable (Function.uncurry Φ) (I.prod DX) :=
    Integrable.of_bound hΦm.aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun p ↦ by
      change ‖Φ p.1 p.2‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (hΦb p.1 p.2).1]; exact (hΦb p.1 p.2).2))
  have hNint : Integrable (fun p : (Fin m → cube d × Bool) × cube d ↦ nnDist p.1 p.2)
      (I.prod DX) :=
    Integrable.of_bound measurable_nnDist.aestronglyMeasurable (Real.sqrt d)
      (Filter.Eventually.of_forall (fun p ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (nnDist_nonneg _ _)]; exact nnDist_le _ _))
  have hL : ∫ S, risk loss01 (condLaw DX η) (h m S) ∂I = ∫ x, ∫ S, Φ S x ∂I ∂DX := by
    rw [← integral_integral_swap hΦint]
    congr 1; funext S
    exact risk_condLaw hηm hη01 ((hmeas m).comp measurable_prodMk_left)
  have hR : ∫ p, nnDist p.1 p.2 ∂(I.prod DX) = ∫ x, ∫ S, nnDist S x ∂I ∂DX :=
    integral_prod_symm _ hNint
  have hbm : Measurable (bayesRule η) := by
    unfold bayesRule
    refine measurable_to_countable' (fun b ↦ ?_)
    cases b
    · have : (fun x ↦ decide (1 / 2 < η x)) ⁻¹' {false} = {x | 1 / 2 < η x}ᶜ := by
        ext x; simp
      rw [this]; exact (measurableSet_lt measurable_const hηm).compl
    · have : (fun x ↦ decide (1 / 2 < η x)) ⁻¹' {true} = {x | 1 / 2 < η x} := by
        ext x; simp
      rw [this]; exact measurableSet_lt measurable_const hηm
  have hB : risk loss01 (condLaw DX η) (bayesRule η) =
      ∫ x, bernoulliErr (η x) (bayesRule η x) ∂DX := risk_condLaw hηm hη01 hbm
  rw [hL, hR, hB]
  -- pointwise estimate
  have key : ∀ x, ∫ S, Φ S x ∂I ≤
      2 * bernoulliErr (η x) (bayesRule η x) + c * ∫ S, nnDist S x ∂I := by
    intro x
    have hΦx : Integrable (fun S ↦ Φ S x) I :=
      Integrable.of_bound (hΦm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun S ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hΦb S x).1]; exact (hΦb S x).2))
    have hNx : Integrable (fun S ↦ nnDist S x) I :=
      Integrable.of_bound (measurable_nnDist.comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable (Real.sqrt d)
        (Filter.Eventually.of_forall (fun S ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (nnDist_nonneg _ _)]; exact nnDist_le _ _))
    rw [hIdef, integral_iid_condLaw hηm hη01 m _ hΦx, integral_iid_condLaw hηm hη01 m _ hNx]
    have hint1 := integrable_decomp hηm hη01 m _ hΦx
    have hint2 := integrable_decomp hηm hη01 m _ hNx
    calc ∫ xs, ∑ ys : Fin m → Bool, (∏ i, wt η (xs i) (ys i)) * Φ (zipL ys xs) x ∂(iidLaw DX m)
        ≤ ∫ xs, (2 * bernoulliErr (η x) (bayesRule η x) + c *
            ∑ ys : Fin m → Bool, (∏ i, wt η (xs i) (ys i)) * nnDist (zipL ys xs) x)
            ∂(iidLaw DX m) := by
          apply integral_mono hint1 ((integrable_const _).add (hint2.const_mul _))
          intro xs
          -- the chosen neighbor
          set j := π m xs x (Fin.castLE hm 0) with hj
          have hΦeq : ∀ ys : Fin m → Bool,
              bernoulliErr (η x) (h m (zipL ys xs) x) = bernoulliErr (η x) (ys j) := by
            intro ys
            rw [hrule m hm (zipL ys xs) x]
            rfl
          have hNeq : ∀ ys : Fin m → Bool, nnDist (zipL ys xs) x = ⨅ i, dist x (xs i) := by
            intro ys; rfl
          show ∑ ys : Fin m → Bool, (∏ i, wt η (xs i) (ys i)) *
              bernoulliErr (η x) (h m (zipL ys xs) x) ≤ 2 * bernoulliErr (η x) (bayesRule η x) +
              c * ∑ ys : Fin m → Bool, (∏ i, wt η (xs i) (ys i)) * nnDist (zipL ys xs) x
          simp_rw [hΦeq, hNeq]
          rw [sum_prod_marginal (fun i b ↦ wt η (xs i) b) (fun i ↦ wt_sum η (xs i)) j
              (fun b ↦ bernoulliErr (η x) b)]
          rw [← Finset.sum_mul, sum_prod_one (fun i b ↦ wt η (xs i) b) (fun i ↦ wt_sum η (xs i)),
            one_mul]
          -- distance to the chosen neighbor is the nearest-neighbor distance
          have hdist : dist x (xs j) ≤ ⨅ i, dist x (xs i) := by
            have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
            apply le_ciInf
            intro i
            have := hsort m xs x (Fin.castLE hm 0) ((π m xs x).symm i)
              (by simp [Fin.le_def])
            simpa using this
          have hlip : |η x - η (xs j)| ≤ c * dist x (xs j) := by
            have := hη.dist_le_mul x (xs j)
            rwa [Real.dist_eq] at this
          have hc0 : (0 : ℝ) ≤ c := c.2
          have hcd : (c : ℝ) * dist x (xs j) ≤ c * ⨅ i, dist x (xs i) :=
            mul_le_mul_of_nonneg_left hdist hc0
          have h01 := hη01 x
          have h01' := hη01 (xs j)
          simp only [wt, bernoulliErr, bayesRule, if_true, Bool.false_eq_true, if_false]
          simp only [Set.mem_Icc] at h01 h01'
          have habs := abs_le.mp (le_trans hlip hcd)
          by_cases hhalf : 1 / 2 < η x
          · simp only [hhalf, decide_true, if_true]
            nlinarith [habs.1, habs.2]
          · simp only [hhalf, decide_false, Bool.false_eq_true, if_false]
            nlinarith [habs.1, habs.2]
      _ = 2 * bernoulliErr (η x) (bayesRule η x) + c *
            ∫ xs, ∑ ys : Fin m → Bool, (∏ i, wt η (xs i) (ys i)) * nnDist (zipL ys xs) x
              ∂(iidLaw DX m) := by
          rw [integral_add (integrable_const _) (hint2.const_mul _), integral_const_mul (c : ℝ)]
          simp
  -- integrate the pointwise estimate
  have hint_left : Integrable (fun x ↦ ∫ S, Φ S x ∂I) DX := hΦint.integral_prod_right
  have hint_N : Integrable (fun x ↦ ∫ S, nnDist S x ∂I) DX := hNint.integral_prod_right
  have hint_B : Integrable (fun x ↦ bernoulliErr (η x) (bayesRule η x)) DX := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall (fun x ↦ ?_))
    · unfold bernoulliErr
      exact (Measurable.ite (hbm (MeasurableSet.singleton true))
        (measurable_const.sub hηm) hηm).aestronglyMeasurable
    · have := hη01 x
      unfold bernoulliErr
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [this.2])]; linarith [this.1]
      · rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  calc ∫ x, ∫ S, Φ S x ∂I ∂DX
      ≤ ∫ x, (2 * bernoulliErr (η x) (bayesRule η x) + c * ∫ S, nnDist S x ∂I) ∂DX :=
        integral_mono hint_left ((hint_B.const_mul 2).add (hint_N.const_mul _)) key
    _ = _ := by
        rw [integral_add (hint_B.const_mul 2) (hint_N.const_mul _), integral_const_mul,
          integral_const_mul]
