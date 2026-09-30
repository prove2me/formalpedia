-- Prove2me | solution 1 for UnderstandingML.sgd_convex_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:00:35.206208+00:00
-- url     : https://prove2.me/submissions/580188bc-8ec7-4ec4-ae42-877e0e6a6721

import Theorems.Thm_UnderstandingML_gd_lemma
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

lemma integral_indep_coord {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {T : ℕ} (i : Fin T) (Ψ : (Fin T → Z) → Z → ℝ)
    (hΨm : Measurable (Function.uncurry Ψ)) (C : ℝ) (hΨb : ∀ S z, |Ψ S z| ≤ C)
    (hΨi : ∀ S z', Ψ (Function.update S i z') = Ψ S) :
    ∫ S, Ψ S (S i) ∂(Measure.pi fun _ => D) = ∫ S, ∫ z, Ψ S z ∂D ∂(Measure.pi fun _ => D) := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by have := i.pos; omega⟩
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) i with he
  have hmp : MeasurePreserving e (Measure.pi fun _ => D)
      (D.prod (Measure.pi fun _ : Fin n => D)) := measurePreserving_piFinSuccAbove (fun _ => D) i
  have hmp' := hmp.symm
  rw [← hmp'.integral_comp' (fun S => Ψ S (S i)), ← hmp'.integral_comp' (fun S => ∫ z, Ψ S z ∂D)]
  have hsymm : ∀ p : Z × (Fin n → Z), e.symm p = i.insertNth p.1 p.2 := fun p => rfl
  have key : ∀ (z z' : Z) (S' : Fin n → Z), Ψ (i.insertNth z S') = Ψ (i.insertNth z' S') := by
    intro z z' S'
    have := hΨi (i.insertNth z' S') z
    rwa [@Fin.update_insertNth n (fun _ => Z) i z' z S'] at this
  set K : (Fin n → Z) → Z → ℝ := fun S' z => Ψ (i.insertNth z S') z with hK
  have hKm : Measurable (Function.uncurry K) := by
    have : Measurable fun q : (Fin n → Z) × Z => (e.symm (q.2, q.1), q.2) :=
      (e.symm.measurable.comp (measurable_snd.prodMk measurable_fst)).prodMk measurable_snd
    exact hΨm.comp this
  have h1 : ∀ p : Z × (Fin n → Z), Ψ (e.symm p) ((e.symm p) i) = K p.2 p.1 := by
    intro p; simp [hsymm, hK]
  have h2 : ∀ p : Z × (Fin n → Z), ∫ z, Ψ (e.symm p) z ∂D = ∫ z, K p.2 z ∂D := by
    intro p
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hsymm, hK]; rw [key p.1 z p.2]
  simp_rw [h1, h2]
  have hint1 : Integrable (fun p : Z × (Fin n → Z) => K p.2 p.1)
      (D.prod (Measure.pi fun _ : Fin n => D)) := by
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun p => ?_)
    · exact (hKm.comp (measurable_snd.prodMk measurable_fst)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hΨb _ _
  have hGm : StronglyMeasurable fun S' : Fin n → Z => ∫ z, K S' z ∂D :=
    hKm.stronglyMeasurable.integral_prod_right'
  have hint2 : Integrable (fun p : Z × (Fin n → Z) => ∫ z, K p.2 z ∂D)
      (D.prod (Measure.pi fun _ : Fin n => D)) := by
    refine Integrable.of_bound (hGm.comp_measurable measurable_snd).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => ?_)
    have := norm_integral_le_of_norm_le_const (μ := D) (f := fun z => K p.2 z) (C := C)
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hΨb _ _)
    simpa using this
  rw [integral_prod_symm _ hint1, integral_prod _ hint2]
  simp


section SGDCommon

variable {d : ℕ} {Z : Type*}

/-- The direction used by SGD at step `t` on sample `S` (zero after `T` steps). -/
noncomputable def sgdDir (η : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) (t : ℕ) :
    Vec d :=
  if h : t < T then g (sgdIterates η g S t) (S ⟨t, h⟩) else 0

lemma sgdIterates_eq_gdIterates (η : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) :
    ∀ t, sgdIterates η g S t = gdIterates η (sgdDir η g S) t
  | 0 => rfl
  | t + 1 => by
    simp only [sgdIterates, gdIterates, sgdDir]
    rw [← sgdIterates_eq_gdIterates η g S t]

lemma sgdIterates_update (η : ℝ) (g : Vec d → Z → Vec d) {T : ℕ} (S : Fin T → Z) (i : Fin T)
    (z : Z) : ∀ t, t ≤ i.val → sgdIterates η g (Function.update S i z) t = sgdIterates η g S t
  | 0, _ => rfl
  | t + 1, ht => by
    simp only [sgdIterates]
    rw [sgdIterates_update η g S i z t (by omega)]
    congr 2
    split_ifs with h
    · rw [Function.update_of_ne]
      intro hti; rw [← hti] at ht; simp at ht
    · rfl

lemma measurable_sgdIterates [MeasurableSpace Z] (η : ℝ) (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (T : ℕ) :
    ∀ t, Measurable fun S : Fin T → Z => sgdIterates η g S t
  | 0 => measurable_const
  | t + 1 => by
    simp only [sgdIterates]
    have ih := measurable_sgdIterates η g hg T t
    by_cases h : t < T
    · simp only [h, dite_true]
      exact ih.sub ((hg.comp (ih.prodMk (measurable_pi_apply (⟨t, h⟩ : Fin T)))).const_smul η)
    · simp only [h, dite_false, smul_zero, sub_zero]; exact ih

lemma norm_sgdIterates_le (η : ℝ) (hη : 0 ≤ η) (g : Vec d → Z → Vec d) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hgb : ∀ w z, ‖g w z‖ ≤ ρ) {T : ℕ} (S : Fin T → Z) :
    ∀ t, ‖sgdIterates η g S t‖ ≤ t * (η * ρ)
  | 0 => by simp [sgdIterates]
  | t + 1 => by
    have ih := norm_sgdIterates_le η hη g hρ hgb S t
    simp only [sgdIterates]
    have hdir : ‖(if h : t < T then g (sgdIterates η g S t) (S ⟨t, h⟩) else 0)‖ ≤ ρ := by
      split_ifs
      · exact hgb _ _
      · simpa using hρ
    calc _ ≤ ‖sgdIterates η g S t‖ + ‖η • (if h : t < T then g (sgdIterates η g S t)
            (S ⟨t, h⟩) else 0)‖ := norm_sub_le _ _
      _ ≤ t * (η * ρ) + η * ρ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
          gcongr
      _ = ((t + 1 : ℕ) : ℝ) * (η * ρ) := by push_cast; ring

end SGDCommon


/-- Integrability of a bounded measurable real function under a probability measure. -/
lemma integrable_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {F : α → ℝ} (hF : Measurable F) (K : ℝ) (hK : ∀ a, |F a| ≤ K) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hK a)

/-- The integrand `⟪w⁽ⁱ⁾ − w⋆, g(w⁽ⁱ⁾, z)⟫`. -/
noncomputable def sgdPsi {d : ℕ} {Z : Type*} (η : ℝ) (g : Vec d → Z → Vec d) (wstar : Vec d)
    {T : ℕ} (i : Fin T) (S : Fin T → Z) (z : Z) : ℝ :=
  ⟪sgdIterates η g S i - wstar, g (sgdIterates η g S i) z⟫_ℝ

theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z] (f : Vec d → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (D : Measure Z) [IsProbabilityMeasure D]
    (g : Vec d → Z → Vec d) (hg : Measurable (Function.uncurry g))
    (horacle : IsSubgradientOracle f D g) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hbound : ∀ w z, ‖g w z‖ ≤ ρ) (wstar : Vec d) (hw : ‖wstar‖ ≤ B) (T : ℕ) (hT : 0 < T) :
    (∫ S, f (sgdAverage (B / (ρ * Real.sqrt T)) g S) ∂(iidLaw D T)) - f wstar ≤
        B * ρ / Real.sqrt T ∧
    ∀ ε : ℝ, 0 < ε → B ^ 2 * ρ ^ 2 / ε ^ 2 ≤ T →
      (∫ S, f (sgdAverage (B / (ρ * Real.sqrt T)) g S) ∂(iidLaw D T)) - f wstar ≤ ε := by
  have hμ : IsProbabilityMeasure (iidLaw D T) := by unfold iidLaw; infer_instance
  set μ := iidLaw D T with hμdef
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  set η := B / (ρ * Real.sqrt T) with hηdef
  have hη : 0 < η := by positivity
  have hWm : ∀ t, Measurable fun S : Fin T → Z => sgdIterates η g S t :=
    measurable_sgdIterates η g hg T
  set R : ℝ := T * (η * ρ) with hR
  have hWb : ∀ i : Fin T, ∀ S : Fin T → Z, ‖sgdIterates η g S i‖ ≤ R := by
    intro i S
    refine (norm_sgdIterates_le η hη.le g hρ.le hbound S i).trans ?_
    have : ((i : ℕ) : ℝ) ≤ T := by exact_mod_cast i.2.le
    exact mul_le_mul_of_nonneg_right this (by positivity)
  -- continuity and boundedness of `f` on the ball of radius `R`
  have hcont : Continuous f := continuousOn_univ.1 (hf.continuousOn isOpen_univ)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Vec d) R).exists_bound_of_continuousOn
    hcont.continuousOn
  have hfb : ∀ u : Vec d, ‖u‖ ≤ R → |f u| ≤ K := fun u hu => by
    rw [← Real.norm_eq_abs]; exact hK u (by simpa using hu)
  -- the average stays in the ball
  have havg : ∀ S : Fin T → Z, ‖sgdAverage η g S‖ ≤ R := by
    intro S
    have hc : Convex ℝ (Metric.closedBall (0 : Vec d) R) := convex_closedBall _ _
    have := hc.sum_mem (t := Finset.range T) (w := fun _ => (T : ℝ)⁻¹)
      (z := fun t => sgdIterates η g S t) (fun _ _ => by positivity)
      (by simp [Finset.card_range]; field_simp) (fun t ht => by
        simpa using hWb ⟨t, Finset.mem_range.1 ht⟩ S)
    simpa [sgdAverage, Finset.smul_sum] using this
  have hgint : ∀ u, Integrable (g u) D := fun u =>
    Integrable.of_bound hg.of_uncurry_left.aestronglyMeasurable ρ
      (Filter.Eventually.of_forall fun z => hbound u z)
  -- integrability
  have hfWint : ∀ i : Fin T, Integrable (fun (S : Fin T → Z) => f (sgdIterates η g S i)) μ := fun i =>
    integrable_of_bdd μ (hcont.measurable.comp (hWm i)) K fun (S : Fin T → Z) => hfb _ (hWb i S)
  have hfavg : Integrable (fun (S : Fin T → Z) => f (sgdAverage η g S)) μ :=
    integrable_of_bdd μ (hcont.measurable.comp (by
      unfold sgdAverage
      exact (Finset.measurable_sum _ fun t _ => hWm t).const_smul ((T : ℝ)⁻¹))) K
      fun (S : Fin T → Z) => hfb _ (havg S)
  have hΨm : ∀ i, Measurable (Function.uncurry (sgdPsi η g wstar i)) := fun i => by
    unfold sgdPsi
    exact Measurable.inner (((hWm i).comp measurable_fst).sub measurable_const)
      (hg.comp (((hWm i).comp measurable_fst).prodMk measurable_snd))
  have hΨb : ∀ (i : Fin T) (S : Fin T → Z) z, |sgdPsi η g wstar i S z| ≤ (R + ‖wstar‖) * ρ := by
    intro i S z
    refine (abs_real_inner_le_norm (sgdIterates η g S i - wstar) _).trans ?_
    have h1 : ‖sgdIterates η g S i - wstar‖ ≤ R + ‖wstar‖ :=
      (norm_sub_le _ _).trans (by linarith [hWb i S])
    exact mul_le_mul h1 (hbound _ _) (norm_nonneg _) (by linarith [norm_nonneg (sgdIterates η g S i - wstar), h1])
  have hΨint : ∀ i : Fin T, Integrable (fun (S : Fin T → Z) => sgdPsi η g wstar i S (S i)) μ := fun i =>
    integrable_of_bdd μ (by
      have h1 : Measurable fun S : Fin T → Z => (S, S i) :=
        measurable_id.prodMk (measurable_pi_apply i)
      have h2 := (hΨm i).comp h1
      simp only [Function.comp_def, Function.uncurry_apply_pair] at h2
      exact h2)
      _ fun (S : Fin T → Z) => hΨb i S (S i)
  have hΨ2m : ∀ i, Measurable fun (S : Fin T → Z) => ∫ z, sgdPsi η g wstar i S z ∂D := fun i =>
    ((hΨm i).stronglyMeasurable.integral_prod_right' (ν := D)).measurable
  have hΨ2int : ∀ i : Fin T, Integrable (fun (S : Fin T → Z) => ∫ z, sgdPsi η g wstar i S z ∂D) μ := by
    intro i
    refine integrable_of_bdd μ (hΨ2m i) ((R + ‖wstar‖) * ρ) fun (S : Fin T → Z) => ?_
    have := norm_integral_le_of_norm_le_const (μ := D) (f := fun z => sgdPsi η g wstar i S z)
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hΨb i S z)
    simpa using this
  -- independence: `E⟪w_t - w⋆, v_t⟫ = E⟪w_t - w⋆, E_z g(w_t, z)⟫`
  have hindep : ∀ i : Fin T, ∫ S, sgdPsi η g wstar i S (S i) ∂μ = ∫ S, ∫ z, sgdPsi η g wstar i S z ∂D ∂μ := fun i =>
    integral_indep_coord D i (sgdPsi η g wstar i) (hΨm i) _ (hΨb i) fun S z' => by
      funext z; unfold sgdPsi; rw [sgdIterates_update η g S i z' i le_rfl]
  -- subgradient inequality in expectation
  have hsubE : ∀ i : Fin T, ∫ S, f (sgdIterates η g S i) ∂μ - f wstar ≤ ∫ S, sgdPsi η g wstar i S (S i) ∂μ := by
    intro i
    rw [hindep i]
    have hpt : ∀ S : Fin T → Z, f (sgdIterates η g S i) - f wstar ≤ ∫ z, sgdPsi η g wstar i S z ∂D := by
      intro S
      simp only [sgdPsi]
      rw [integral_inner (hgint _)]
      have := horacle (sgdIterates η g S i) wstar
      have e : ⟪wstar - sgdIterates η g S i, ∫ z, g (sgdIterates η g S i) z ∂D⟫_ℝ =
          -⟪sgdIterates η g S i - wstar, ∫ z, g (sgdIterates η g S i) z ∂D⟫_ℝ := by rw [← inner_neg_left, neg_sub]
      linarith
    have := integral_mono (μ := μ) (f := fun S => f (sgdIterates η g S i) - f wstar)
      (g := fun S => ∫ z, sgdPsi η g wstar i S z ∂D)
      ((hfWint i).sub (integrable_const (f wstar))) (hΨ2int i) hpt
    rwa [integral_sub (hfWint i) (integrable_const _), integral_const, probReal_univ,
      one_smul] at this
  -- pathwise Lemma 14.1
  have hpath : ∀ S : Fin T → Z, ∑ i : Fin T, sgdPsi η g wstar i S (S i) ≤ B * ρ / Real.sqrt T * T := by
    intro S
    have hvb : ∀ t < T, ‖sgdDir η g S t‖ ≤ ρ := by
      intro t ht; simp only [sgdDir, ht, dite_true]; exact hbound _ _
    have hgd := (UnderstandingML.gd_lemma (sgdDir η g S) T wstar).2 B ρ hB hρ hvb hw hT
    rw [← Fin.sum_univ_eq_sum_range] at hgd
    have hdir : ∀ i : Fin T, sgdDir η g S i = g (sgdIterates η g S i) (S i) := by
      intro i; simp [sgdDir, i.2]
    rw [← hηdef] at hgd
    simp only [← sgdIterates_eq_gdIterates, hdir] at hgd
    rwa [div_le_iff₀ hTpos] at hgd
  have hsumE : ∑ i : Fin T, ∫ S, sgdPsi η g wstar i S (S i) ∂μ ≤ B * ρ / Real.sqrt T * T := by
    rw [← integral_finsetSum _ fun i _ => hΨint i]
    have := integral_mono (integrable_finsetSum _ fun i _ => hΨint i)
      (integrable_const (B * ρ / Real.sqrt T * T)) hpath
    rwa [integral_const, probReal_univ, one_smul] at this
  -- Jensen
  have hjensen : ∀ S : Fin T → Z, f (sgdAverage η g S) ≤
      (T : ℝ)⁻¹ * ∑ i : Fin T, f (sgdIterates η g S i) := by
    intro S
    have := hf.map_sum_le (t := Finset.range T) (w := fun _ => (T : ℝ)⁻¹)
      (p := fun t => sgdIterates η g S t) (fun _ _ => by positivity)
      (by simp [Finset.card_range]; field_simp) (fun _ _ => Set.mem_univ _)
    rw [Fin.sum_univ_eq_sum_range (fun t => f (sgdIterates η g S t)) T, Finset.mul_sum]
    simpa [sgdAverage, Finset.smul_sum] using this
  have hmain : ∫ S, f (sgdAverage η g S) ∂μ - f wstar ≤ B * ρ / Real.sqrt T := by
    have h1 : ∫ S, f (sgdAverage η g S) ∂μ ≤ (T : ℝ)⁻¹ * ∑ i : Fin T, ∫ S, f (sgdIterates η g S i) ∂μ := by
      rw [← integral_finsetSum _ fun i _ => hfWint i, ← integral_const_mul]
      exact integral_mono hfavg ((integrable_finsetSum _ fun i _ => hfWint i).const_mul _)
        hjensen
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hsubE i
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h2
    have h3 : (T : ℝ)⁻¹ * ∑ i : Fin T, ∫ S, f (sgdIterates η g S i) ∂μ - f wstar =
        (T : ℝ)⁻¹ * (∑ i : Fin T, ∫ S, f (sgdIterates η g S i) ∂μ - T * f wstar) := by
      field_simp
    have h4 : (T : ℝ)⁻¹ * (∑ i : Fin T, ∫ S, f (sgdIterates η g S i) ∂μ - T * f wstar) ≤
        (T : ℝ)⁻¹ * (B * ρ / Real.sqrt T * T) := by
      gcongr; linarith
    have h5 : (T : ℝ)⁻¹ * (B * ρ / Real.sqrt T * T) = B * ρ / Real.sqrt T := by field_simp
    linarith
  refine ⟨hmain, fun ε hε hTε => hmain.trans ?_⟩
  rw [div_le_iff₀ hs]
  have : B * ρ / ε ≤ Real.sqrt T := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, mul_pow]; exact hTε
  rw [div_le_iff₀ hε] at this
  linarith
