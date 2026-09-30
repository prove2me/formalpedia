-- Prove2me | solution 1 for UnderstandingML.knn_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T08:16:44.404189+00:00
-- url     : https://prove2.me/submissions/49740d10-a166-4d74-9766-fb824a01c081

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


open MeasureTheory

namespace KnnLabel

/-- The analytic core: `log t + (n-1) log (1-t) + n t ≤ log (1/√n)` for `n ≥ 4`, `t ∈ (0,1)`. -/
lemma key_analytic (n : ℝ) (hn : 4 ≤ n) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    Real.log t + (n - 1) * Real.log (1 - t) + n * t ≤ Real.log (1 / Real.sqrt n) := by
  set u := 1 / Real.sqrt n with hu_def
  have hsn : 2 ≤ Real.sqrt n := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hn
  have hu0 : 0 < u := by positivity
  have hu2 : u ≤ 1 / 2 := by
    rw [hu_def]; exact one_div_le_one_div_of_le (by norm_num) hsn
  have hnu : n * u ^ 2 = 1 := by
    rw [hu_def, div_pow, Real.sq_sqrt (by linarith)]; field_simp
  have hn_eq : n = 1 / u ^ 2 := by field_simp; linarith
  have h1 : Real.log t ≤ Real.log u + t / u - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos ht0 hu0)
    rw [Real.log_div ht0.ne' hu0.ne'] at this; linarith
  have h2 : Real.log (1 - t) ≤ Real.log (1 - u) + (u - t) / (1 - u) := by
    have hu1 : 0 < 1 - u := by linarith
    have := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1 - t) hu1)
    rw [Real.log_div (by linarith) hu1.ne'] at this
    have e : (1 - t) / (1 - u) - 1 = (u - t) / (1 - u) := by field_simp; ring
    linarith
  have h3 : Real.log (1 - u) ≤ -(2 * u / (2 - u)) := by
    have hu1 : 0 < 1 - u := by linarith
    have := Real.le_log_one_add_of_nonneg (x := u / (1 - u)) (by positivity)
    have e1 : 1 + u / (1 - u) = (1 - u)⁻¹ := by field_simp; ring
    have hu2' : (2 - u) ≠ 0 := by intro h; linarith
    have e2 : 2 * (u / (1 - u)) / (u / (1 - u) + 2) = 2 * u / (2 - u) := by
      have h3 : u / (1 - u) + 2 = (2 - u) / (1 - u) := by field_simp; ring
      rw [h3, ← mul_div_assoc, div_div_div_cancel_right₀ hu1.ne']
    rw [e1, Real.log_inv, e2] at this; linarith
  have hn1 : 0 ≤ n - 1 := by linarith
  have hB : (n - 1) * Real.log (1 - t) ≤ (n - 1) * (-(2 * u / (2 - u)) + (u - t) / (1 - u)) := by
    apply mul_le_mul_of_nonneg_left _ hn1; linarith
  have hfinal : t / u - 1 + (n - 1) * (-(2 * u / (2 - u)) + (u - t) / (1 - u)) + n * t =
      (2 * u - 1) / (2 - u) := by
    rw [hn_eq]
    have hu1 : (1 - u) ≠ 0 := by intro h; linarith
    have hu2' : (2 - u) ≠ 0 := by intro h; linarith
    field_simp
    ring
  have hneg : (2 * u - 1) / (2 - u) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith

/-- Weight of a label vector. -/
def W {k : ℕ} (p : Fin k → ℝ) (Z : Fin k → Bool) : ℝ := ∏ i, (if Z i then p i else 1 - p i)

/-- Number of ones. -/
def cnt {k : ℕ} (Z : Fin k → Bool) : ℝ := ∑ i, if Z i then (1 : ℝ) else 0

lemma W_nonneg {k : ℕ} {p : Fin k → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (Z : Fin k → Bool) :
    0 ≤ W p Z :=
  Finset.prod_nonneg (fun i _ ↦ by
    have := hp i; split_ifs <;> linarith [this.1, this.2])

lemma sum_W {k : ℕ} (p : Fin k → ℝ) : ∑ Z, W p Z = 1 := by
  unfold W
  have h := Fintype.prod_sum (fun (i : Fin k) (b : Bool) ↦ if b then p i else 1 - p i)
  rw [← h]
  simp

lemma sum_W_cnt {k : ℕ} (p : Fin k → ℝ) : ∑ Z, W p Z * cnt Z = ∑ i, p i := by
  unfold cnt
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; funext j
  have key : ∀ Z : Fin k → Bool, W p Z * (if Z j then (1 : ℝ) else 0) =
      ∏ i, ((if Z i then p i else 1 - p i) * (if i = j then (if Z i then 1 else 0) else 1)) := by
    intro Z
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j]
    simp [W]
  simp_rw [key]
  have h := Fintype.prod_sum (fun (i : Fin k) (b : Bool) ↦ (if b then p i else 1 - p i) *
    (if i = j then (if b then (1 : ℝ) else 0) else 1))
  rw [← h, Finset.prod_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

/-- Chernoff's bound for sums of independent (non-identical) Bernoulli variables. -/
lemma chernoff {k : ℕ} {p : Fin k → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∑ Z, W p Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0) ≤
      Real.exp (-τ * k / 2 + (∑ i, p i) * (Real.exp τ - 1)) := by
  calc ∑ Z, W p Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0)
      ≤ ∑ Z, W p Z * Real.exp (τ * (cnt Z - k / 2)) := by
        apply Finset.sum_le_sum; intro Z _
        apply mul_le_mul_of_nonneg_left _ (W_nonneg hp Z)
        split_ifs with h
        · exact Real.one_le_exp (mul_nonneg hτ (by linarith))
        · exact (Real.exp_pos _).le
    _ = Real.exp (-τ * k / 2) * ∏ i, (1 - p i + p i * Real.exp τ) := by
        have e : ∀ Z : Fin k → Bool, W p Z * Real.exp (τ * (cnt Z - k / 2)) =
            Real.exp (-τ * k / 2) * ∏ i, ((if Z i then p i else 1 - p i) *
              (if Z i then Real.exp τ else 1)) := by
          intro Z
          rw [Finset.prod_mul_distrib, W]
          have : Real.exp (τ * (cnt Z - k / 2)) = Real.exp (-τ * k / 2) *
              ∏ i, (if Z i then Real.exp τ else 1) := by
            have hsplit : τ * (cnt Z - k / 2) = -τ * k / 2 + ∑ i, (if Z i then τ else 0) := by
              unfold cnt
              rw [mul_sub, Finset.mul_sum]
              simp only [mul_ite, mul_one, mul_zero]
              ring
            rw [hsplit, Real.exp_add, Real.exp_sum]
            congr 1; apply Finset.prod_congr rfl; intro i _; split_ifs <;> simp
          rw [this]; ring
        simp_rw [e]
        have h := Fintype.prod_sum (fun (i : Fin k) (b : Bool) ↦ (if b then p i else 1 - p i) *
          (if b then Real.exp τ else 1))
        rw [← Finset.mul_sum, ← h]
        congr 1; apply Finset.prod_congr rfl; intro i _
        simp; ring
    _ ≤ Real.exp (-τ * k / 2) * ∏ i, Real.exp (p i * (Real.exp τ - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Finset.prod_le_prod
        · intro i _
          have h1 := hp i
          have h2 := mul_nonneg h1.1 (Real.exp_pos τ).le
          linarith [h1.2]
        · intro i _
          have := Real.add_one_le_exp (p i * (Real.exp τ - 1))
          linarith
    _ = _ := by
        rw [← Real.exp_sum, ← Real.exp_add, Finset.sum_mul]


lemma sqrt_eight_div (k : ℕ) (hk : 0 < k) : Real.sqrt (8 / k) = 2 / Real.sqrt ((k : ℝ) / 2) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [show (8 : ℝ) / k = 4 / ((k : ℝ) / 2) by field_simp; norm_num, Real.sqrt_div (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The tail estimate: `(1 - 2P) · P[#ones ≥ k/2] ≤ √(8/k) · P` when the mean `P ≤ 1/2`. -/
lemma tail_bound {k : ℕ} (hk : 10 ≤ k) {p : Fin k → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hP : (∑ i, p i) / k ≤ 1 / 2) :
    (1 - 2 * ((∑ i, p i) / k)) * ∑ Z, W p Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0) ≤
      Real.sqrt (8 / k) * ((∑ i, p i) / k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set P := (∑ i, p i) / k with hPdef
  have hsum : ∑ i, p i = k * P := by rw [hPdef]; field_simp
  have hP0 : 0 ≤ P := div_nonneg (Finset.sum_nonneg (fun i _ ↦ (hp i).1)) hk'.le
  set Q := ∑ Z, W p Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0) with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun Z _ ↦ mul_nonneg (W_nonneg hp Z) (by split_ifs <;> norm_num))
  have ht0 : 0 ≤ 1 - 2 * P := by linarith
  rcases eq_or_lt_of_le hP0 with hPz | hPpos
  · -- Markov
    have hmarkov : Q ≤ 2 * P := by
      calc Q ≤ ∑ Z, W p Z * (cnt Z / ((k : ℝ) / 2)) := by
            apply Finset.sum_le_sum; intro Z _
            apply mul_le_mul_of_nonneg_left _ (W_nonneg hp Z)
            split_ifs with h
            · rw [le_div_iff₀ (by positivity)]; linarith
            · exact div_nonneg (Finset.sum_nonneg (fun i _ ↦ by split_ifs <;> norm_num))
                (by positivity)
        _ = (∑ Z, W p Z * cnt Z) / ((k : ℝ) / 2) := by
            rw [Finset.sum_div]; congr 1; funext Z; ring
        _ = 2 * P := by rw [sum_W_cnt, hsum]; field_simp
    rw [← hPz] at hmarkov ⊢
    have : Q ≤ 0 := by linarith
    nlinarith
  rcases eq_or_lt_of_le hP with hPh | hPlt
  · rw [hPh]; norm_num; positivity
  -- Chernoff at `e^τ = 1/(2P)`
  set τ := Real.log (1 / (2 * P)) with hτ
  have h2P : 0 < 2 * P := by linarith
  have hτ0 : 0 ≤ τ := Real.log_nonneg (by rw [le_div_iff₀ h2P]; linarith)
  have hch := chernoff hp τ hτ0
  have hexpτ : Real.exp τ = 1 / (2 * P) := Real.exp_log (by positivity)
  set n : ℝ := (k : ℝ) / 2 with hn
  set t : ℝ := 1 - 2 * P with ht
  have hexp_eq : -τ * k / 2 + (∑ i, p i) * (Real.exp τ - 1) = n * Real.log (1 - t) + n * t := by
    rw [hexpτ, hsum, hτ, one_div, Real.log_inv, ht, hn]
    field_simp
    ring
  rw [hexp_eq] at hch
  have htpos : 0 < t := by rw [ht]; linarith
  have ht1 : t < 1 := by rw [ht]; linarith
  have hn4 : 4 ≤ n := by
    rw [hn]; have : (10 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hkey := key_analytic n hn4 t htpos ht1
  have h1t : 0 < 1 - t := by linarith
  calc t * Q ≤ t * Real.exp (n * Real.log (1 - t) + n * t) :=
        mul_le_mul_of_nonneg_left hch htpos.le
    _ = Real.exp (Real.log t + n * Real.log (1 - t) + n * t) := by
        rw [add_assoc, Real.exp_add (Real.log t) _, Real.exp_log htpos]
    _ ≤ Real.exp (Real.log (1 - t) + Real.log (1 / Real.sqrt n)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = (1 - t) / Real.sqrt n := by
        rw [Real.exp_add, Real.exp_log h1t, Real.exp_log (by positivity)]; ring
    _ = Real.sqrt (8 / k) * P := by
        rw [sqrt_eight_div k (by omega), ← hn, ht]; ring

open UnderstandingML in
/-- finite-sum form of Lemma 19.7 -/
lemma label_sum {k : ℕ} (hk : 10 ≤ k) (p : Fin k → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ Z, W p Z * bernoulliErr ((∑ i, p i) / k) (decide ((k : ℝ) / 2 < cnt Z)) ≤
      (1 + Real.sqrt (8 / k)) * bernoulliErr ((∑ i, p i) / k) (decide (1 / 2 < (∑ i, p i) / k)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set P := (∑ i, p i) / k with hPdef
  have hsplit : ∀ Z, W p Z * bernoulliErr P (decide ((k : ℝ) / 2 < cnt Z)) =
      W p Z * P + (1 - 2 * P) * (W p Z * (if (k : ℝ) / 2 < cnt Z then 1 else 0)) := by
    intro Z; unfold bernoulliErr; split_ifs with h1 h2 <;> simp_all <;> ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_W, one_mul, ← Finset.mul_sum]
  by_cases hhalf : 1 / 2 < P
  · -- flip the labels
    simp only [hhalf, decide_true, bernoulliErr, if_true]
    let p' : Fin k → ℝ := fun i ↦ 1 - p i
    have hp' : ∀ i, p' i ∈ Set.Icc (0 : ℝ) 1 := fun i ↦
      ⟨by linarith [(hp i).2], by linarith [(hp i).1]⟩
    have hP' : (∑ i, p' i) / k = 1 - P := by
      simp only [p', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      rw [hPdef]; field_simp
    have htb := tail_bound hk hp' (by rw [hP']; linarith)
    rw [hP'] at htb
    let σ : (Fin k → Bool) ≃ (Fin k → Bool) :=
      { toFun := fun Z i ↦ !Z i, invFun := fun Z i ↦ !Z i,
        left_inv := fun Z ↦ by funext i; simp, right_inv := fun Z ↦ by funext i; simp }
    have hW : ∀ Z, W p' (σ Z) = W p Z := by
      intro Z; unfold W; apply Finset.prod_congr rfl; intro i _
      simp only [σ, Equiv.coe_fn_mk, p']
      by_cases h : Z i = true <;> simp [h]
    have hcnt : ∀ Z, cnt (σ Z) = k - cnt Z := by
      intro Z; unfold cnt
      rw [show (k : ℝ) = ∑ _i : Fin k, (1 : ℝ) by simp, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      simp only [σ, Equiv.coe_fn_mk]
      by_cases h : Z i = true <;> simp [h]
    have hflip : ∑ Z, W p' Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0) =
        1 - ∑ Z, W p Z * (if (k : ℝ) / 2 < cnt Z then 1 else 0) := by
      rw [← Equiv.sum_comp σ]
      simp_rw [hW, hcnt]
      rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
      conv_rhs => rw [← sum_W p]
      apply Finset.sum_congr rfl; intro Z _
      split_ifs with h1 h2 h2 <;> first | (exfalso; linarith) | ring
    rw [hflip] at htb
    have hs8 : 0 ≤ Real.sqrt (8 / k) := Real.sqrt_nonneg _
    nlinarith [htb]
  · simp only [hhalf, decide_false, bernoulliErr, Bool.false_eq_true, if_false]
    push Not at hhalf
    have htb := tail_bound hk hp hhalf
    have hle : ∑ Z, W p Z * (if (k : ℝ) / 2 < cnt Z then 1 else 0) ≤
        ∑ Z, W p Z * (if (k : ℝ) / 2 ≤ cnt Z then 1 else 0) := by
      apply Finset.sum_le_sum; intro Z _
      apply mul_le_mul_of_nonneg_left _ (W_nonneg hp Z)
      split_ifs with h1 h2 <;> first | (exfalso; linarith) | norm_num
    have ht0 : 0 ≤ 1 - 2 * P := by linarith
    have := mul_le_mul_of_nonneg_left hle ht0
    nlinarith [htb]

end KnnLabel


open MeasureTheory

namespace KnnErr

open UnderstandingML NNInfra KnnLabel

/-- product over the image of an injective map -/
lemma prod_ite_range {k m : ℕ} (J : Fin k → Fin m) (hJ : Function.Injective J)
    (f : Fin m → ℝ) :
    ∏ i, (if i ∈ Set.range J then f i else 1) = ∏ l, f (J l) := by
  classical
  have : (∏ i, (if i ∈ Set.range J then f i else 1)) = ∏ i ∈ Finset.univ.image J, f i := by
    rw [← Finset.prod_filter]
    congr 1; ext i; simp
  rw [this, Finset.prod_image (fun a _ b _ h ↦ hJ h)]

/-- marginalization over the labels not selected by an injective map -/
lemma sum_prod_comp_inj {k m : ℕ} [Nonempty (Fin k)] (J : Fin k → Fin m) (hJ : Function.Injective J)
    (w : Fin m → Bool → ℝ) (hw : ∀ i, w i true + w i false = 1) (φ : (Fin k → Bool) → ℝ) :
    ∑ ys : Fin m → Bool, (∏ i, w i (ys i)) * φ (fun l ↦ ys (J l)) =
      ∑ z : Fin k → Bool, (∏ l, w (J l) (z l)) * φ z := by
  classical
  have key : ∀ z : Fin k → Bool, ∑ ys : Fin m → Bool,
      (∏ i, w i (ys i)) * (if (fun l ↦ ys (J l)) = z then (1 : ℝ) else 0) = ∏ l, w (J l) (z l) := by
    intro z
    let g : Fin m → Bool → ℝ := fun i b ↦
      if i ∈ Set.range J then (if b = z (Function.invFun J i) then 1 else 0) else 1
    have hg : ∀ ys : Fin m → Bool,
        (if (fun l ↦ ys (J l)) = z then (1 : ℝ) else 0) = ∏ i, g i (ys i) := by
      intro ys
      rw [show (∏ i, g i (ys i)) = ∏ i, (if i ∈ Set.range J then
          (if ys i = z (Function.invFun J i) then (1 : ℝ) else 0) else 1) from rfl,
        prod_ite_range J hJ (fun i ↦ if ys i = z (Function.invFun J i) then (1 : ℝ) else 0)]
      simp only [Function.leftInverse_invFun hJ _]
      rw [Finset.prod_boole]
      simp [funext_iff]
    simp_rw [hg, ← Finset.prod_mul_distrib]
    have h := Fintype.prod_sum (fun (i : Fin m) (b : Bool) ↦ w i b * g i b)
    rw [← h]
    have h2 : ∀ i, ∑ b, w i b * g i b =
        if i ∈ Set.range J then w i (z (Function.invFun J i)) else 1 := by
      intro i
      by_cases hi : i ∈ Set.range J
      · simp only [g, hi, if_true, Fintype.sum_bool]
        cases z (Function.invFun J i) <;> simp
      · simp only [g, hi, if_false, Fintype.sum_bool, mul_one]; exact hw i
    simp_rw [h2]
    rw [prod_ite_range J hJ (fun i ↦ w i (z (Function.invFun J i)))]
    simp only [Function.leftInverse_invFun hJ _]
  calc ∑ ys : Fin m → Bool, (∏ i, w i (ys i)) * φ (fun l ↦ ys (J l))
      = ∑ ys : Fin m → Bool, ∑ z : Fin k → Bool,
          (∏ i, w i (ys i)) * (if (fun l ↦ ys (J l)) = z then (1 : ℝ) else 0) * φ z := by
        apply Finset.sum_congr rfl; intro ys _
        simp [mul_ite]
    _ = ∑ z : Fin k → Bool, (∏ l, w (J l) (z l)) * φ z := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro z _
        rw [← key z, Finset.sum_mul]

/-- the grid index of a point of the cube -/
noncomputable def idx {d : ℕ} (T : ℕ) (x : cube d) : Fin d → Fin (T + 1) :=
  fun j ↦ ⟨min ⌊((T + 1 : ℕ) : ℝ) * x.1.ofLp j⌋₊ T, by omega⟩

lemma measurable_idx {d : ℕ} (T : ℕ) : Measurable (idx (d := d) T) := by
  apply measurable_pi_lambda
  intro j
  have h1 : Measurable (fun x : cube d ↦ ⌊((T + 1 : ℕ) : ℝ) * x.1.ofLp j⌋₊) := by
    apply Nat.measurable_floor.comp
    apply Measurable.const_mul
    exact (measurable_pi_apply j).comp ((PiLp.continuous_ofLp 2 _).measurable.comp measurable_subtype_coe)
  have h2 : Measurable (fun x : cube d ↦ min ⌊((T + 1 : ℕ) : ℝ) * x.1.ofLp j⌋₊ T) :=
    (measurable_from_top (f := fun n : ℕ ↦ min n T)).comp h1
  refine measurable_to_countable' (fun r ↦ ?_)
  convert h2 (measurableSet_singleton r.val) using 1
  ext x; simp [idx, Fin.ext_iff]

lemma coord_bounds (T : ℕ) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ((min ⌊((T + 1 : ℕ) : ℝ) * u⌋₊ T : ℕ) : ℝ) / (T + 1 : ℕ) ≤ u ∧
      u ≤ ((min ⌊((T + 1 : ℕ) : ℝ) * u⌋₊ T : ℕ) + 1 : ℝ) / (T + 1 : ℕ) := by
  have hT : (0 : ℝ) < (T + 1 : ℕ) := by positivity
  have h0 : 0 ≤ ((T + 1 : ℕ) : ℝ) * u := mul_nonneg hT.le hu.1
  rw [div_le_iff₀ hT, le_div_iff₀ hT]
  rcases le_total ⌊((T + 1 : ℕ) : ℝ) * u⌋₊ T with h | h
  · rw [min_eq_left h]
    refine ⟨?_, ?_⟩
    · have := Nat.floor_le h0; linarith
    · have := Nat.lt_floor_add_one (((T + 1 : ℕ) : ℝ) * u); linarith
  · rw [min_eq_right h]
    have h' : (T : ℝ) ≤ ⌊((T + 1 : ℕ) : ℝ) * u⌋₊ := by exact_mod_cast h
    have := Nat.floor_le h0
    push_cast at *
    constructor <;> nlinarith [hu.2]

lemma idx_close {d : ℕ} (T : ℕ) (x y : cube d) (h : idx T x = idx T y) :
    dist x y ≤ Real.sqrt d / (T + 1 : ℕ) := by
  have hT : (0 : ℝ) < (T + 1 : ℕ) := by positivity
  rw [Subtype.dist_eq, EuclideanSpace.dist_eq]
  have hc : ∀ j, dist (x.1.ofLp j) (y.1.ofLp j) ^ 2 ≤ (1 / (T + 1 : ℕ)) ^ 2 := by
    intro j
    have hj := congrFun h j
    simp only [idx, Fin.mk.injEq] at hj
    have hx := coord_bounds T _ (x.2 j)
    have hy := coord_bounds T _ (y.2 j)
    rw [hj] at hx
    rw [Real.dist_eq, sq_abs]
    have e : ((min ⌊((T + 1 : ℕ) : ℝ) * y.1.ofLp j⌋₊ T : ℕ) + 1 : ℝ) / (T + 1 : ℕ) =
      ((min ⌊((T + 1 : ℕ) : ℝ) * y.1.ofLp j⌋₊ T : ℕ) : ℝ) / (T + 1 : ℕ) + 1 / (T + 1 : ℕ) := by
      ring
    rw [e] at hx hy
    have : |x.1.ofLp j - y.1.ofLp j| ≤ 1 / (T + 1 : ℕ) := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc Real.sqrt (∑ j, dist (x.1.ofLp j) (y.1.ofLp j) ^ 2)
      ≤ Real.sqrt (∑ _j : Fin d, (1 / (T + 1 : ℕ) : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum (fun j _ ↦ hc j))
    _ = Real.sqrt d / (T + 1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.sqrt_mul
          (by positivity), Real.sqrt_sq (by positivity)]
        ring

/-- if at least `k` sample points are within `δ`, the `k` nearest neighbors are within `δ` -/
lemma kth_close {d k m : ℕ} (hk : k ≤ m) (xs : Fin m → cube d) (x : cube d)
    (π : Fin m ≃ Fin m) (hsort : ∀ i j : Fin m, i ≤ j → dist x (xs (π i)) ≤ dist x (xs (π j)))
    (δ : ℝ) (hcard : k ≤ (Finset.univ.filter (fun i ↦ dist x (xs i) ≤ δ)).card)
    (l : Fin k) : dist x (xs (π (Fin.castLE hk l))) ≤ δ := by
  set S := Finset.univ.filter (fun i ↦ dist x (xs i) ≤ δ) with hS
  have : ∃ i ∈ S, Fin.castLE hk l ≤ π.symm i := by
    by_contra H
    push Not at H
    have hsub : S.map π.symm.toEmbedding ⊆ Finset.Iio (Fin.castLE hk l) := by
      intro j hj
      rw [Finset.mem_map] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      exact Finset.mem_Iio.mpr (H i hi)
    have := Finset.card_le_card hsub
    rw [Finset.card_map, Fin.card_Iio] at this
    simp at this
    omega
  obtain ⟨i, hi, hle⟩ := this
  have h1 := hsort _ _ hle
  rw [Equiv.apply_symm_apply] at h1
  exact h1.trans (Finset.mem_filter.mp hi).2

/-- pointwise label estimate from Lemma 19.7 -/
lemma label_pointwise {k : ℕ} (hk : 10 ≤ k) (p : Fin k → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (e : ℝ) (ε : ℝ) (hε : ∀ l, |e - p l| ≤ ε) :
    ∑ Z, W p Z * bernoulliErr e (decide ((k : ℝ) / 2 < cnt Z)) ≤
      (1 + Real.sqrt (8 / k)) * bernoulliErr e (decide (1 / 2 < e)) + 3 * ε := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set P := (∑ i, p i) / k with hPdef
  have hP : |e - P| ≤ ε := by
    have : e - P = (∑ i, (e - p i)) / k := by
      rw [hPdef, Finset.sum_sub_distrib]; simp; field_simp
    rw [this, abs_div, abs_of_pos hk', div_le_iff₀ hk']
    calc |∑ i, (e - p i)| ≤ ∑ i, |e - p i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, ε := Finset.sum_le_sum (fun i _ ↦ hε i)
      _ = ε * k := by simp [mul_comm]
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hP
  have hs1 : Real.sqrt (8 / k) ≤ 1 := by
    rw [Real.sqrt_le_one]
    rw [div_le_one hk']
    exact_mod_cast (by omega : 8 ≤ k)
  have hs0 : 0 ≤ Real.sqrt (8 / k) := Real.sqrt_nonneg _
  have herr : ∀ b, bernoulliErr e b ≤ bernoulliErr P b + ε := by
    intro b; have := abs_le.mp hP; cases b <;> simp [bernoulliErr] <;> linarith
  have h1 : ∑ Z, W p Z * bernoulliErr e (decide ((k : ℝ) / 2 < cnt Z)) ≤
      ∑ Z, W p Z * bernoulliErr P (decide ((k : ℝ) / 2 < cnt Z)) + ε := by
    calc ∑ Z, W p Z * bernoulliErr e (decide ((k : ℝ) / 2 < cnt Z))
        ≤ ∑ Z, W p Z * (bernoulliErr P (decide ((k : ℝ) / 2 < cnt Z)) + ε) :=
          Finset.sum_le_sum (fun Z _ ↦ mul_le_mul_of_nonneg_left (herr _) (W_nonneg hp Z))
      _ = _ := by simp_rw [mul_add]; rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_W, one_mul]
  have h2 := label_sum hk p hp
  have h3 : bernoulliErr P (decide (1 / 2 < P)) ≤ bernoulliErr e (decide (1 / 2 < e)) + ε := by
    have := abs_le.mp hP
    by_cases h1 : 1 / 2 < P <;> by_cases h2 : 1 / 2 < e <;> simp only [bernoulliErr, h1, h2, decide_true, decide_false, if_true, if_false, Bool.false_eq_true] <;> linarith
  nlinarith

/-- numeric few-points estimate -/
lemma few_numeric {k m : ℕ} (hk : 10 ≤ k) (hm : 0 < m) (q ψ : ℝ) (hq : 0 ≤ q) (hψ1 : ψ ≤ 1)
    (hψ0 : 0 ≤ ψ) (hψ : ψ ≤ Real.exp ((k : ℝ) / 3 - 5 * q * m / 18)) :
    q * ψ ≤ 3 * k / (2 * m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  rw [le_div_iff₀ (by positivity)]
  by_cases hqm : q * m ≤ 3 / 2 * k
  · nlinarith
  · push Not at hqm
    set u := q * m / 18 with hu
    have hu0 : 0 ≤ u := by positivity
    have h1 : ψ ≤ Real.exp (-u) := hψ.trans (Real.exp_le_exp.mpr (by rw [hu]; nlinarith))
    have h2 : 1 + u + u ^ 2 / 2 ≤ Real.exp u := Real.quadratic_le_exp_of_nonneg hu0
    have h3 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-u) := Real.exp_pos _
    have h5 : 2 * u * Real.exp (-u) ≤ 1 := by nlinarith
    have : q * ψ * (2 * m) = 36 * u * ψ := by rw [hu]; ring
    rw [this]
    nlinarith

/-- Chernoff lower tail for the number of sample points in a set -/
lemma count_tail {X : Type*} [MeasurableSpace X] (DX : Measure X) [IsProbabilityMeasure DX]
    (C : Set X) (hC : MeasurableSet C) (k m : ℕ) :
    ∫ xs, (if (∑ i, (C.indicator (fun _ ↦ (1 : ℝ)) (xs i))) < k then (1 : ℝ) else 0)
      ∂(iidLaw DX m) ≤ Real.exp ((k : ℝ) / 3 - 5 * DX.real C * m / 18) := by
  have hI := iid_isProb DX m
  set q := DX.real C with hq
  set t : ℝ := 1 / 3 with ht
  let f : X → ℝ := fun y ↦ Real.exp (-t * C.indicator (fun _ ↦ (1 : ℝ)) y)
  have hfm : Measurable f := by
    apply Real.measurable_exp.comp
    exact (measurable_const.indicator hC).const_mul _
  have hf01 : ∀ y, 0 ≤ f y ∧ f y ≤ 1 := by
    intro y; refine ⟨(Real.exp_pos _).le, ?_⟩
    apply Real.exp_le_one_iff.mpr
    by_cases hy : y ∈ C <;> simp [hy, ht]
  have hfint : Integrable f DX :=
    Integrable.of_bound hfm.aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf01 y).1]; exact (hf01 y).2))
  have hpt : ∀ xs : Fin m → X,
      (if (∑ i, (C.indicator (fun _ ↦ (1 : ℝ)) (xs i))) < k then (1 : ℝ) else 0) ≤
        Real.exp (t * k) * ∏ i, f (xs i) := by
    intro xs
    rw [← Real.exp_sum, ← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      have htpos : 0 < t := by rw [ht]; norm_num
      have := mul_lt_mul_of_pos_left h htpos
      rw [← Finset.mul_sum]; linarith
    · exact (Real.exp_pos _).le
  have hprod_int : Integrable (fun xs : Fin m → X ↦ ∏ i, f (xs i)) (iidLaw DX m) := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall (fun xs ↦ ?_))
    · exact (Finset.measurable_prod _ (fun i _ ↦ hfm.comp (measurable_pi_apply i))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i _ ↦ (hf01 _).1))]
      exact Finset.prod_le_one (fun i _ ↦ (hf01 _).1) (fun i _ ↦ (hf01 _).2)
  have hintf : ∫ y, f y ∂DX = 1 - (1 - Real.exp (-t)) * q := by
    have : f = fun y ↦ 1 + (Real.exp (-t) - 1) * C.indicator (fun _ ↦ (1 : ℝ)) y := by
      funext y; by_cases hy : y ∈ C <;> simp [f, hy]
    rw [this, integral_add (integrable_const _) ((integrable_const _).indicator hC |>.const_mul _),
      integral_const_mul, integral_indicator hC]
    simp [hq, measureReal_restrict_apply]; ring
  have hq01 : 0 ≤ q ∧ q ≤ 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have het : Real.exp (-t) ≤ 13 / 18 := by
    have h1 := Real.quadratic_le_exp_of_nonneg (x := t) (by rw [ht]; norm_num)
    have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (-t)
    rw [ht] at h1
    nlinarith
  have het0 : 0 < Real.exp (-t) := Real.exp_pos _
  calc ∫ xs, (if (∑ i, (C.indicator (fun _ ↦ (1 : ℝ)) (xs i))) < k then (1 : ℝ) else 0)
        ∂(iidLaw DX m)
      ≤ ∫ xs, Real.exp (t * k) * ∏ i, f (xs i) ∂(iidLaw DX m) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun xs ↦ by
          positivity)) (hprod_int.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = Real.exp (t * k) * (1 - (1 - Real.exp (-t)) * q) ^ m := by
        rw [integral_const_mul, iidLaw, integral_fintype_prod_eq_prod (𝕜 := ℝ) (fun _ y ↦ f y),
          hintf]
        simp
    _ ≤ Real.exp (t * k) * Real.exp (-(1 - Real.exp (-t)) * q) ^ m := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply pow_le_pow_left₀ (by nlinarith)
        have := Real.add_one_le_exp (-(1 - Real.exp (-t)) * q)
        linarith
    _ ≤ Real.exp ((k : ℝ) / 3 - 5 * q * m / 18) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hm0 : (0 : ℝ) ≤ m := by positivity
        rw [ht]
        nlinarith [mul_nonneg hq01.1 hm0]

end KnnErr


open MeasureTheory

namespace KnnErr

open UnderstandingML NNInfra KnnLabel

/-- indicator that the box `r` contains fewer than `k` sample points -/
noncomputable def few {d m : ℕ} (T k : ℕ) (xs : Fin m → cube d) (r : Fin d → Fin (T + 1)) : ℝ :=
  if (∑ i, ({y | idx T y = r}.indicator (fun _ ↦ (1 : ℝ)) (xs i))) < k then 1 else 0

lemma few_nonneg {d m : ℕ} (T k : ℕ) (xs : Fin m → cube d) (r : Fin d → Fin (T + 1)) :
    0 ≤ few T k xs r := by unfold few; split_ifs <;> norm_num

lemma few_le_one {d m : ℕ} (T k : ℕ) (xs : Fin m → cube d) (r : Fin d → Fin (T + 1)) :
    few T k xs r ≤ 1 := by unfold few; split_ifs <;> norm_num

lemma measurable_few {d m : ℕ} (T k : ℕ) (r : Fin d → Fin (T + 1)) :
    Measurable (fun xs : Fin m → cube d ↦ few T k xs r) := by
  have hC : MeasurableSet {y : cube d | idx T y = r} :=
    measurable_idx T (MeasurableSet.singleton r)
  have hN : Measurable (fun xs : Fin m → cube d ↦
      ∑ i, ({y | idx T y = r}.indicator (fun _ ↦ (1 : ℝ)) (xs i))) :=
    Finset.measurable_sum _ (fun i _ ↦
      (measurable_const.indicator hC).comp (measurable_pi_apply i))
  unfold few
  exact Measurable.ite (measurableSet_lt hN measurable_const) measurable_const measurable_const

/-- the pointwise estimate for a fixed sample of instances and a fixed query point -/
lemma pointwise {d : ℕ} (η : cube d → ℝ) (c : NNReal) (hη : LipschitzWith c η)
    (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : 10 ≤ k) (h : Learner (cube d × Bool) (cube d → Bool)) (hnn : IsKNNRule k h)
    (m : ℕ) (hm : k ≤ m) (T : ℕ) (xs : Fin m → cube d) (x : cube d) :
    ∑ ys : Fin m → Bool, (∏ i, wt η (xs i) (ys i)) * bernoulliErr (η x) (h m (zipL ys xs) x) ≤
      (1 + Real.sqrt (8 / k)) * bernoulliErr (η x) (bayesRule η x) +
        3 * c * Real.sqrt d / (T + 1 : ℕ) + few T k xs (idx T x) := by
  classical
  obtain ⟨π, hsort, hrule⟩ := hnn
  set J : Fin k → Fin m := fun l ↦ π m xs x (Fin.castLE hm l) with hJdef
  have hJ : Function.Injective J := (π m xs x).injective.comp (Fin.castLE_injective hm)
  have hrw : ∀ ys : Fin m → Bool, h m (zipL ys xs) x = majority (fun l ↦ ys (J l)) := by
    intro ys; rw [hrule m hm (zipL ys xs) x]; rfl
  simp_rw [hrw]
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  rw [sum_prod_comp_inj J hJ (fun i b ↦ wt η (xs i) b) (fun i ↦ wt_sum η (xs i))
    (fun z ↦ bernoulliErr (η x) (majority z))]
  set p : Fin k → ℝ := fun l ↦ η (xs (J l)) with hpdef
  have hp : ∀ l, p l ∈ Set.Icc (0 : ℝ) 1 := fun l ↦ hη01 _
  have hW : ∀ z : Fin k → Bool, (∏ l, wt η (xs (J l)) (z l)) = W p z := by
    intro z; simp only [W, wt, hpdef]
  have hM : ∀ z : Fin k → Bool, majority z = decide ((k : ℝ) / 2 < cnt z) := by
    intro z; simp [majority, cnt]
  simp_rw [hW, hM]
  have hs0 : 0 ≤ Real.sqrt (8 / k) := Real.sqrt_nonneg _
  have herr01 : ∀ e : ℝ, e ∈ Set.Icc (0 : ℝ) 1 → ∀ b, 0 ≤ bernoulliErr e b ∧ bernoulliErr e b ≤ 1 := by
    intro e he b; cases b <;> simp [bernoulliErr] <;> constructor <;> linarith [he.1, he.2]
  have hc0 : (0 : ℝ) ≤ c := c.2
  set δ := Real.sqrt d / (T + 1 : ℕ) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  set N := ∑ i, ({y | idx T y = idx T x}.indicator (fun _ ↦ (1 : ℝ)) (xs i)) with hN
  by_cases hc : (k : ℝ) ≤ N
  · have hfew : few T k xs (idx T x) = 0 := by
      unfold few; rw [if_neg (by rw [← hN]; linarith)]
    rw [hfew]
    have hNcard : N = ((Finset.univ.filter (fun i ↦ idx T (xs i) = idx T x)).card : ℝ) := by
      rw [hN, Finset.card_filter]; push_cast
      apply Finset.sum_congr rfl; intro i _
      simp [Set.indicator_apply]
    have hcard : k ≤ (Finset.univ.filter (fun i ↦ dist x (xs i) ≤ δ)).card := by
      have h1 : k ≤ (Finset.univ.filter (fun i ↦ idx T (xs i) = idx T x)).card := by
        rw [hNcard] at hc; exact_mod_cast hc
      refine h1.trans (Finset.card_le_card (Finset.monotone_filter_right _ ?_))
      intro i _ hi
      rw [dist_comm]; exact idx_close T _ _ hi
    have hε : ∀ l, |η x - p l| ≤ c * δ := by
      intro l
      have h1 := hη.dist_le_mul x (xs (J l))
      rw [Real.dist_eq] at h1
      have h2 := kth_close hm xs x (π m xs x) (hsort m xs x) δ hcard l
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hc0)
    have := label_pointwise hk p hp (η x) (c * δ) hε
    have e : 3 * (c * δ) = 3 * c * Real.sqrt d / (T + 1 : ℕ) := by rw [hδ]; ring
    rw [e] at this
    simpa [bayesRule] using this
  · have hfew : few T k xs (idx T x) = 1 := by
      unfold few; rw [if_pos (by rw [← hN]; linarith)]
    rw [hfew]
    have hle : ∑ z, W p z * bernoulliErr (η x) (decide ((k : ℝ) / 2 < cnt z)) ≤ 1 := by
      calc ∑ z, W p z * bernoulliErr (η x) (decide ((k : ℝ) / 2 < cnt z))
          ≤ ∑ z, W p z * 1 := Finset.sum_le_sum (fun z _ ↦
            mul_le_mul_of_nonneg_left (herr01 _ (hη01 x) _).2 (W_nonneg hp z))
        _ = 1 := by simp [sum_W]
    have h1 := (herr01 _ (hη01 x) (bayesRule η x)).1
    have h2 : 0 ≤ 3 * c * Real.sqrt d / (T + 1 : ℕ) := by positivity
    nlinarith

theorem main_bound (d : ℕ) (DX : Measure (cube d)) [IsProbabilityMeasure DX]
    (η : cube d → ℝ) (c : NNReal) (hη : LipschitzWith c η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : 10 ≤ k) (h : Learner (cube d × Bool) (cube d → Bool)) (hnn : IsKNNRule k h)
    (hmeas : ∀ m, Measurable (fun p : (Fin m → cube d × Bool) × cube d ↦ h m p.1 p.2))
    (m : ℕ) (hm : k ≤ m) (T : ℕ) :
    ∫ S, risk loss01 (condLaw DX η) (h m S) ∂(iidLaw (condLaw DX η) m) ≤
      (1 + Real.sqrt (8 / k)) * risk loss01 (condLaw DX η) (bayesRule η) +
        3 * c * Real.sqrt d / (T + 1 : ℕ) +
        ∑ r, (DX.map (idx T)).real {r} * ∫ xs, few T k xs r ∂(iidLaw DX m) := by
  classical
  have hηm : Measurable η := hη.continuous.measurable
  have hD := condLaw_isProb (DX := DX) hηm hη01
  have hI := iid_isProb (condLaw DX η) m
  have hIX := iid_isProb DX m
  set I := iidLaw (condLaw DX η) m with hIdef
  set s := Real.sqrt (8 / k) with hsdef
  set B := 3 * c * Real.sqrt d / (T + 1 : ℕ) with hBdef
  let ψ : (Fin d → Fin (T + 1)) → ℝ := fun r ↦ ∫ xs, few T k xs r ∂(iidLaw DX m)
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
  have hL : ∫ S, risk loss01 (condLaw DX η) (h m S) ∂I = ∫ x, ∫ S, Φ S x ∂I ∂DX := by
    rw [← integral_integral_swap hΦint]
    congr 1; funext S
    exact risk_condLaw hηm hη01 ((hmeas m).comp measurable_prodMk_left)
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
  have hψ01 : ∀ r, 0 ≤ ψ r ∧ ψ r ≤ 1 := by
    intro r
    refine ⟨integral_nonneg (fun xs ↦ few_nonneg _ _ _ _), ?_⟩
    calc ψ r ≤ ∫ _xs, (1 : ℝ) ∂(iidLaw DX m) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun xs ↦ few_nonneg _ _ _ _))
            (integrable_const _) (Filter.Eventually.of_forall (fun xs ↦ few_le_one _ _ _ _))
      _ = 1 := by simp
  have hψint : Integrable (fun x ↦ ψ (idx T x)) DX :=
    Integrable.of_bound ((measurable_of_countable ψ).comp (measurable_idx T)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall (fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hψ01 _).1]; exact (hψ01 _).2))
  have hψsum : ∫ x, ψ (idx T x) ∂DX = ∑ r, (DX.map (idx T)).real {r} * ψ r := by
    rw [← integral_map (measurable_idx T).aemeasurable
      (measurable_of_countable ψ).aestronglyMeasurable, integral_fintype Integrable.of_finite]
    rfl
  rw [hL, hB, ← hψsum]
  have key : ∀ x, ∫ S, Φ S x ∂I ≤
      (1 + s) * bernoulliErr (η x) (bayesRule η x) + B + ψ (idx T x) := by
    intro x
    have hΦx : Integrable (fun S ↦ Φ S x) I :=
      Integrable.of_bound (hΦm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun S ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hΦb S x).1]; exact (hΦb S x).2))
    have hfx : Integrable (fun xs ↦ few T k xs (idx T x)) (iidLaw DX m) :=
      Integrable.of_bound (measurable_few T k (idx T x)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun xs ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (few_nonneg _ _ _ _)]; exact few_le_one _ _ _ _))
    rw [hIdef, integral_iid_condLaw hηm hη01 m _ hΦx]
    have hint1 := integrable_decomp hηm hη01 m _ hΦx
    calc ∫ xs, ∑ ys : Fin m → Bool, (∏ i, wt η (xs i) (ys i)) * Φ (zipL ys xs) x ∂(iidLaw DX m)
        ≤ ∫ xs, ((1 + s) * bernoulliErr (η x) (bayesRule η x) + B + few T k xs (idx T x))
            ∂(iidLaw DX m) :=
          integral_mono hint1 (((integrable_const _).add (integrable_const _)).add hfx)
            (fun xs ↦ pointwise η c hη hη01 k hk h hnn m hm T xs x)
      _ = (1 + s) * bernoulliErr (η x) (bayesRule η x) + B + ψ (idx T x) := by
          rw [integral_add (integrable_const _) hfx]
          simp [ψ]
  have hint_left : Integrable (fun x ↦ ∫ S, Φ S x ∂I) DX := hΦint.integral_prod_right
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
      ≤ ∫ x, ((1 + s) * bernoulliErr (η x) (bayesRule η x) + B + ψ (idx T x)) ∂DX :=
        integral_mono hint_left (((hint_B.const_mul _).add (integrable_const _)).add hψint) key
    _ = _ := by
        have h1 : Integrable (fun x ↦ (1 + s) * bernoulliErr (η x) (bayesRule η x) + B) DX :=
          (hint_B.const_mul _).add (integrable_const _)
        rw [integral_add h1 hψint,
          integral_add (hint_B.const_mul _) (integrable_const _), integral_const_mul]
        simp

end KnnErr


open MeasureTheory

namespace KnnErr

open UnderstandingML NNInfra KnnLabel

lemma risk_nonneg' {d : ℕ} (DX : Measure (cube d)) (η : cube d → ℝ) (g : cube d → Bool) :
    0 ≤ risk loss01 (condLaw DX η) g := by
  unfold risk
  exact integral_nonneg (fun z ↦ by unfold loss01; split_ifs <;> norm_num)

lemma few_sum_bound {d : ℕ} (DX : Measure (cube d)) [IsProbabilityMeasure DX] (k : ℕ)
    (hk : 10 ≤ k) (m : ℕ) (hm : k ≤ m) (T : ℕ) :
    ∑ r, (DX.map (idx T)).real {r} * ∫ xs, few T k xs r ∂(iidLaw DX m) ≤
      3 * k / (2 * m) * ((T + 1 : ℕ) : ℝ) ^ d := by
  have hI := iid_isProb DX m
  have hterm : ∀ r, (DX.map (idx T)).real {r} * ∫ xs, few T k xs r ∂(iidLaw DX m) ≤
      3 * k / (2 * m) := by
    intro r
    rw [map_measureReal_apply (measurable_idx T) (MeasurableSet.singleton r)]
    have hC : MeasurableSet {y : cube d | idx T y = r} :=
      measurable_idx T (MeasurableSet.singleton r)
    apply few_numeric hk (by omega) _ _ measureReal_nonneg
    · calc ∫ xs, few T k xs r ∂(iidLaw DX m) ≤ ∫ _xs, (1 : ℝ) ∂(iidLaw DX m) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall (fun xs ↦ few_nonneg _ _ _ _))
              (integrable_const _) (Filter.Eventually.of_forall (fun xs ↦ few_le_one _ _ _ _))
        _ = 1 := by simp
    · exact integral_nonneg (fun xs ↦ few_nonneg _ _ _ _)
    · have := count_tail DX {y : cube d | idx T y = r} hC k m
      exact this
  calc ∑ r, (DX.map (idx T)).real {r} * ∫ xs, few T k xs r ∂(iidLaw DX m)
      ≤ ∑ _r : Fin d → Fin (T + 1), (3 * k / (2 * m) : ℝ) := Finset.sum_le_sum (fun r _ ↦ hterm r)
    _ = _ := by simp [mul_comm]

lemma few_sum_zero {d : ℕ} (hd : d = 0) (DX : Measure (cube d)) [IsProbabilityMeasure DX] (k : ℕ)
    (m : ℕ) (hm : k ≤ m) (T : ℕ) :
    ∑ r, (DX.map (idx T)).real {r} * ∫ xs, few T k xs r ∂(iidLaw DX m) = 0 := by
  subst hd
  apply Finset.sum_eq_zero
  intro r _
  have : ∀ xs : Fin m → cube 0, few T k xs r = 0 := by
    intro xs
    unfold few
    have h1 : ∀ i, {y : cube 0 | idx T y = r}.indicator (fun _ ↦ (1 : ℝ)) (xs i) = 1 := by
      intro i
      rw [Set.indicator_of_mem]
      exact Subsingleton.elim _ _
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (k : ℝ) ≤ m := by exact_mod_cast hm
    rw [if_neg (by linarith)]
  simp [this]

lemma risk_le_one {d : ℕ} (DX : Measure (cube d)) [IsProbabilityMeasure DX]
    (η : cube d → ℝ) (hη : Measurable η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (h : Learner (cube d × Bool) (cube d → Bool)) (m : ℕ) :
    ∫ S, risk loss01 (condLaw DX η) (h m S) ∂(iidLaw (condLaw DX η) m) ≤ 1 := by
  have hD := condLaw_isProb (DX := DX) hη hη01
  have hI := iid_isProb (condLaw DX η) m
  have hr : ∀ g : cube d → Bool, risk loss01 (condLaw DX η) g ≤ 1 := by
    intro g
    unfold risk
    calc ∫ z, loss01 g z ∂(condLaw DX η) ≤ ∫ _z, (1 : ℝ) ∂(condLaw DX η) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z ↦ by
            unfold loss01; split_ifs <;> norm_num)) (integrable_const _)
            (Filter.Eventually.of_forall (fun z ↦ by unfold loss01; split_ifs <;> norm_num))
      _ = 1 := by simp
  calc ∫ S, risk loss01 (condLaw DX η) (h m S) ∂(iidLaw (condLaw DX η) m)
      ≤ ∫ _S, (1 : ℝ) ∂(iidLaw (condLaw DX η) m) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun S ↦ risk_nonneg' _ _ _))
          (integrable_const _) (Filter.Eventually.of_forall (fun S ↦ hr _))
    _ = 1 := by simp

end KnnErr

open UnderstandingML NNInfra KnnErr in
theorem solution (d : ℕ) (DX : Measure (cube d)) [IsProbabilityMeasure DX]
    (η : cube d → ℝ) (c : NNReal) (hη : LipschitzWith c η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : 10 ≤ k) (h : Learner (cube d × Bool) (cube d → Bool)) (hnn : IsKNNRule k h)
    (hmeas : ∀ m, Measurable (fun p : (Fin m → cube d × Bool) × cube d ↦ h m p.1 p.2))
    (m : ℕ) (hm : k ≤ m) :
    ∫ S, risk loss01 (condLaw DX η) (h m S) ∂(iidLaw (condLaw DX η) m) ≤
      (1 + Real.sqrt (8 / k)) * risk loss01 (condLaw DX η) (bayesRule η) +
        (6 * c * Real.sqrt d + k) * (m : ℝ) ^ (-(1 : ℝ) / (d + 1)) := by
  have hL0 := risk_nonneg' DX η (bayesRule η)
  have hs0 : 0 ≤ Real.sqrt (8 / k) := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hmpos : 0 < (m : ℝ) ^ (-(1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hm0 _
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have hb := main_bound d DX η c hη hη01 k hk h hnn hmeas m hm 0
    rw [few_sum_zero hd DX k m hm 0] at hb
    subst hd
    simp only [CharP.cast_eq_zero, Real.sqrt_zero, mul_zero, zero_div, add_zero, zero_add] at hb ⊢
    have : (0 : ℝ) ≤ k * (m : ℝ) ^ (-(1 : ℝ) / (0 + 1)) := by positivity
    linarith
  · set a := (m : ℝ) ^ ((1 : ℝ) / (d + 1)) with ha
    have ha0 : 0 < a := Real.rpow_pos_of_pos hm0 _
    have hinv : (m : ℝ) ^ (-(1 : ℝ) / (d + 1)) = 1 / a := by
      rw [ha, neg_div, Real.rpow_neg hm0.le, inv_eq_one_div]
    have hma : (m : ℝ) = a ^ (d + 1) := by
      rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
      have : (1 : ℝ) / (d + 1) * ((d + 1 : ℕ) : ℝ) = 1 := by
        push_cast; field_simp
      rw [this, Real.rpow_one]
    rw [hinv]
    by_cases ha10 : a ≤ 10
    · have h1 := risk_le_one DX η hη.continuous.measurable hη01 h m
      have hk1 : (1 : ℝ) ≤ k * (1 / a) := by
        rw [mul_one_div, le_div_iff₀ ha0]
        have : (10 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have : 0 ≤ 6 * c * Real.sqrt d * (1 / a) := by positivity
      nlinarith
    · push Not at ha10
      set T := ⌈a / 2⌉₊ - 1 with hT
      have hT1 : ((T + 1 : ℕ) : ℝ) = ⌈a / 2⌉₊ := by
        have : 0 < ⌈a / 2⌉₊ := Nat.ceil_pos.mpr (by linarith)
        rw [hT]; congr 1; omega
      have hTlo : a / 2 ≤ ((T + 1 : ℕ) : ℝ) := by rw [hT1]; exact Nat.le_ceil _
      have hThi : ((T + 1 : ℕ) : ℝ) ≤ 3 / 5 * a := by
        rw [hT1]; have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ a / 2); linarith
      have hb := main_bound d DX η c hη hη01 k hk h hnn hmeas m hm T
      have hf := few_sum_bound DX k hk m hm T
      have hA : 3 * c * Real.sqrt d / (T + 1 : ℕ) ≤ 6 * c * Real.sqrt d * (1 / a) := by
        rw [div_le_iff₀ (by linarith)]
        have : 0 ≤ 3 * c * Real.sqrt d := by positivity
        have e : 6 * c * Real.sqrt d * (1 / a) * ((T + 1 : ℕ) : ℝ) =
            3 * c * Real.sqrt d * (2 * ((T + 1 : ℕ) : ℝ) / a) := by ring
        rw [e]
        have : 1 ≤ 2 * ((T + 1 : ℕ) : ℝ) / a := by rw [le_div_iff₀ ha0]; linarith
        nlinarith
      have hB : 3 * k / (2 * m) * ((T + 1 : ℕ) : ℝ) ^ d ≤ k * (1 / a) := by
        have hpow : ((T + 1 : ℕ) : ℝ) ^ d ≤ (3 / 5 * a) ^ d :=
          pow_le_pow_left₀ (by positivity) hThi d
        have hpow2 : ((3 : ℝ) / 5) ^ d ≤ 3 / 5 := pow_le_of_le_one (by norm_num) (by norm_num)
          (by omega)
        rw [mul_pow] at hpow
        have hk0 : (0 : ℝ) ≤ k := by positivity
        calc 3 * k / (2 * m) * ((T + 1 : ℕ) : ℝ) ^ d
            ≤ 3 * k / (2 * m) * ((3 / 5) ^ d * a ^ d) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = 3 / 2 * (3 / 5) ^ d * k * (1 / a) := by
              rw [hma, pow_succ]; field_simp
          _ ≤ k * (1 / a) := by
              have : 0 ≤ k * (1 / a) := by positivity
              nlinarith
      nlinarith

