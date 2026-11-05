-- Prove2me | solution 1 for SinkhornDRO.BSMD.lemma_EC_6_I
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T06:26:14.700123+00:00
-- url     : https://prove2.me/submissions/62cbd25e-f8ca-4761-865b-098b8d32ebf0

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_Objective

open MeasureTheory ProbabilityTheory

namespace Aux_BSMD6I
open SinkhornDRO.BSMD

lemma pi_meas {Z : Type*} [MeasurableSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) :
    Measurable (fun x => Measure.pi fun _ : Fin n => Q x) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm
    isPiSystem_pi ?_
  rintro _ ⟨s, hs, rfl⟩
  simp only [Measure.pi_pi]
  exact Finset.measurable_prod _ (fun i _ => Q.measurable_coe (hs i (Set.mem_univ i)))

lemma kern_meas {Z : Type*} [MeasurableSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) :
    Measurable (fun x : Z => (Measure.dirac x).prod (Measure.pi fun _ : Fin n => Q x)) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_prod.symm
    isPiSystem_prod ?_
  rintro _ ⟨A, hA, B, hB, rfl⟩
  simp only [Measure.prod_prod]
  exact ((Measure.measurable_coe (show MeasurableSet A from hA)).comp Measure.measurable_dirac).mul
    ((Measure.measurable_coe (show MeasurableSet B from hB)).comp (pi_meas Q n))

lemma levelLaw_prob {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) : IsProbabilityMeasure (levelLaw P Q n) := by
  constructor
  unfold levelLaw
  rw [Measure.bind_apply MeasurableSet.univ (kern_meas Q n).aemeasurable]
  simp

lemma pi_marg {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) :
    (Measure.pi fun _ : Fin n => μ).map (fun zs => zs ∘ e) = Measure.pi fun _ : Fin m => μ := by
  classical
  have hm : Measurable (fun zs : Fin n → Z => zs ∘ e) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  set t : Fin n → Set Z := Function.extend e s (fun _ => Set.univ) with ht
  have hpre : (fun zs : Fin n → Z => zs ∘ e) ⁻¹' (Set.univ.pi s) = Set.univ.pi t := by
    ext zs
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp]
    constructor
    · intro h i
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        rw [show t (e j) = s j from he.extend_apply s _ j]; exact h j
      · rw [show t i = Set.univ from Function.extend_apply' _ _ _ hi]; trivial
    · intro h j
      have := h (e j)
      rwa [show t (e j) = s j from he.extend_apply s _ j] at this
  rw [hpre, Measure.pi_pi]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image e))]
  · rw [Finset.prod_image (fun a _ b _ h => he h)]
    exact Finset.prod_congr rfl (fun j _ => by rw [show t (e j) = s j from he.extend_apply s _ j])
  · intro i _ hi
    have : ¬ ∃ j, e j = i := by simpa using hi
    rw [show t i = Set.univ from Function.extend_apply' _ _ _ this, measure_univ]

lemma levelLaw_marg {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] {m n : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) :
    (levelLaw P Q n).map (fun ζ : Z × (Fin n → Z) => (ζ.1, ζ.2 ∘ e)) = levelLaw P Q m := by
  have hm : Measurable (fun zs : Fin n → Z => zs ∘ e) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hg : Measurable (fun ζ : Z × (Fin n → Z) => (ζ.1, ζ.2 ∘ e)) :=
    measurable_fst.prodMk (hm.comp measurable_snd)
  ext s hs
  rw [Measure.map_apply hg hs]
  unfold levelLaw
  rw [Measure.bind_apply (hg hs) (kern_meas Q n).aemeasurable,
    Measure.bind_apply hs (kern_meas Q m).aemeasurable]
  refine lintegral_congr (fun x => ?_)
  rw [← Measure.map_apply hg hs]
  congr 1
  have : (fun ζ : Z × (Fin n → Z) => (ζ.1, ζ.2 ∘ e)) = Prod.map id (fun zs => zs ∘ e) := rfl
  rw [this, ← Measure.map_prod_map _ _ measurable_id hm, Measure.map_id, pi_marg (Q x) e he]

lemma integral_marg {Z E : Type*} [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] {m n : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (ψ : Z × (Fin m → Z) → E) (hψ : StronglyMeasurable ψ) :
    ∫ ζ, ψ (ζ.1, ζ.2 ∘ e) ∂(levelLaw P Q n) = ∫ ζ, ψ ζ ∂(levelLaw P Q m) := by
  have hm : Measurable (fun zs : Fin n → Z => zs ∘ e) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have hg : Measurable (fun ζ : Z × (Fin n → Z) => (ζ.1, ζ.2 ∘ e)) :=
    measurable_fst.prodMk (hm.comp measurable_snd)
  rw [← levelLaw_marg P Q e he, integral_map hg.aemeasurable hψ.aestronglyMeasurable]

/-- the kernel `x ↦ δ_x ⊗ Q_x^{⊗ n}` -/
noncomputable def kerN {Z : Type*} [MeasurableSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (n : ℕ) : Kernel Z (Z × (Fin n → Z)) :=
  ⟨fun x => (Measure.dirac x).prod (Measure.pi fun _ : Fin n => Q x), kern_meas Q n⟩

instance kerN_markov {Z : Type*} [MeasurableSpace Z] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (n : ℕ) : IsMarkovKernel (kerN Q n) :=
  ⟨fun x => by unfold kerN; simp only [Kernel.coe_mk]; infer_instance⟩

lemma levelLaw_eq {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) :
    levelLaw P Q n = (kerN Q n ∘ₖ Kernel.const Unit P) () := by
  rw [Kernel.comp_apply, Kernel.const_apply]; rfl

lemma levelLaw_integral {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ) (ψ : Z × (Fin n → Z) → ℝ)
    (hψm : StronglyMeasurable ψ) (hψ : Integrable ψ (levelLaw P Q n)) :
    ∫ ζ, ψ ζ ∂(levelLaw P Q n)
      = ∫ x, ∫ zs, ψ (x, zs) ∂(Measure.pi fun _ : Fin n => Q x) ∂P := by
  rw [levelLaw_eq] at hψ ⊢
  rw [ProbabilityTheory.Kernel.integral_comp hψ, Kernel.const_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ∫ y, ψ y ∂((Measure.dirac x).prod _) = _
  rw [Measure.dirac_prod, integral_map measurable_prodMk_left.aemeasurable
    hψm.aestronglyMeasurable]

lemma levelLaw_integrable_inner {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q] (n : ℕ)
    (ψ : Z × (Fin n → Z) → ℝ) (hψm : StronglyMeasurable ψ) (hψ : Integrable ψ (levelLaw P Q n)) :
    Integrable (fun x => ∫ zs, ψ (x, zs) ∂(Measure.pi fun _ : Fin n => Q x)) P := by
  rw [levelLaw_eq] at hψ
  have := hψ.integral_comp
  rw [Kernel.const_apply] at this
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  show ∫ y, ψ y ∂((Measure.dirac x).prod _) = _
  rw [Measure.dirac_prod, integral_map measurable_prodMk_left.aemeasurable
    hψm.aestronglyMeasurable]

lemma pi_coord_integral {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (i : Fin n) (φ : Z → ℝ) (hφ : Measurable φ) :
    ∫ zs, φ (zs i) ∂(Measure.pi fun _ : Fin n => μ) = ∫ z, φ z ∂μ := by
  have h := (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq
  conv_rhs => rw [← h]
  rw [integral_map (measurable_pi_apply i).aemeasurable hφ.aestronglyMeasurable]

lemma pi_pair_integral {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (i j : Fin n) (hij : i ≠ j) (φ ψ : Z → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    ∫ zs, φ (zs i) * ψ (zs j) ∂(Measure.pi fun _ : Fin n => μ)
      = (∫ z, φ z ∂μ) * ∫ z, ψ z ∂μ := by
  have he : Function.Injective (![i, j] : Fin 2 → Fin n) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have hm : Measurable (fun zs : Fin n → Z => zs ∘ ![i, j]) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have h1 := integral_map hm.aemeasurable (μ := Measure.pi fun _ : Fin n => μ)
    (f := fun w : Fin 2 → Z => φ (w 0) * ψ (w 1))
    ((hφ.comp (measurable_pi_apply 0)).mul (hψ.comp (measurable_pi_apply 1))).aestronglyMeasurable
  rw [pi_marg μ _ he] at h1
  simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
  rw [← h1]
  have := integral_fin_nat_prod_eq_prod (μ := fun _ : Fin 2 => μ) (![φ, ψ] : Fin 2 → Z → ℝ)
  simpa [Fin.prod_univ_two] using this

lemma pi_var {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {n : ℕ} (σ : Fin n → ℝ) (φ : Z → ℝ) (hφ : Measurable φ) (R : ℝ) (hR : ∀ z, |φ z| ≤ R)
    (h0 : ∫ z, φ z ∂μ = 0) :
    ∫ zs, (∑ j, σ j * φ (zs j)) ^ 2 ∂(Measure.pi fun _ : Fin n => μ)
      = (∑ j, σ j ^ 2) * ∫ z, φ z ^ 2 ∂μ := by
  have hint : ∀ i j : Fin n, Integrable (fun zs : Fin n → Z => σ i * φ (zs i) * (σ j * φ (zs j)))
      (Measure.pi fun _ : Fin n => μ) := by
    intro i j
    refine Integrable.of_bound (((measurable_const.mul (hφ.comp (measurable_pi_apply i))).mul
      (measurable_const.mul (hφ.comp (measurable_pi_apply j))))).aestronglyMeasurable
      (|σ i| * R * (|σ j| * R)) (Filter.Eventually.of_forall fun zs => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have := hR (zs i); have := hR (zs j)
    have h0R : 0 ≤ R := (abs_nonneg _).trans (hR (zs i))
    gcongr
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j)),
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum _ (fun j _ => hint i j), Finset.sum_eq_single i]
  · have e : ∀ zs : Fin n → Z, σ i * φ (zs i) * (σ i * φ (zs i)) = σ i * σ i * (φ (zs i) * φ (zs i)) :=
      fun zs => by ring
    simp_rw [e]
    rw [integral_const_mul, pi_coord_integral μ i (fun z => φ z * φ z) (hφ.mul hφ)]
  · intro j _ hji
    have e : ∀ zs : Fin n → Z, σ i * φ (zs i) * (σ j * φ (zs j)) = σ i * σ j * (φ (zs i) * φ (zs j)) :=
      fun zs => by ring
    simp_rw [e]
    rw [integral_const_mul, pi_pair_integral μ i j (Ne.symm hji) φ φ hφ hφ, h0]
    ring
  · simp


end Aux_BSMD6I

open SinkhornDRO.BSMD Aux_BSMD6I in
theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (Θ : Set (Param d)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Kernel Z Z) [IsMarkovKernel Q]
    (lam eps : ℝ) (hlam : 0 < lam) (heps : 0 < eps)
    (f : Param d → Z → ℝ) (hf_meas : ∀ θ, Measurable (f θ))
    (B : ℝ) (hA2III : Asm2Bounded Θ f B) (ℓ : ℕ) :
    ∀ θ ∈ Θ, |objFℓ P Q lam eps f ℓ θ - objF P Q lam eps f θ|
      ≤ lam * eps * Real.exp (2 * (B / (lam * eps))) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ := by
  intro θ hθ
  have := levelLaw_prob P Q (2 ^ ℓ)
  have ha : 0 < lam * eps := mul_pos hlam heps
  obtain ⟨z0⟩ := nonempty_of_isProbabilityMeasure P
  set E := Real.exp (B / (lam * eps)) with hE
  have he1 : ∀ z, 1 ≤ Real.exp (f θ z / (lam * eps)) := fun z =>
    Real.one_le_exp (div_nonneg (hA2III θ hθ z).1 ha.le)
  have heE : ∀ z, Real.exp (f θ z / (lam * eps)) ≤ E := fun z =>
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hA2III θ hθ z).2 ha.le)
  have hE1 : 1 ≤ E := (he1 z0).trans (heE z0)
  have hem : Measurable (fun z => Real.exp (f θ z / (lam * eps))) :=
    Real.measurable_exp.comp ((hf_meas θ).div_const _)
  set n : ℝ := (2 : ℝ) ^ ℓ with hn_def
  have hn : 0 < n := by positivity
  have hcard : ((Finset.univ : Finset (Fin (2 ^ ℓ))).card : ℝ) = n := by
    rw [Finset.card_univ, Fintype.card_fin]; push_cast; rfl
  set Y : (Fin (2 ^ ℓ) → Z) → ℝ := fun zs => n⁻¹ * ∑ j, Real.exp (f θ (zs j) / (lam * eps))
    with hY
  have hY1 : ∀ zs, 1 ≤ Y zs := by
    intro zs
    have := Finset.card_nsmul_le_sum Finset.univ (fun j => Real.exp (f θ (zs j) / (lam * eps))) 1
      (fun j _ => he1 _)
    rw [nsmul_eq_mul, mul_one, hcard] at this
    simp only [hY]
    rw [← div_eq_inv_mul, le_div_iff₀ hn]; linarith
  have hYE : ∀ zs, Y zs ≤ E := by
    intro zs
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => Real.exp (f θ (zs j) / (lam * eps))) E
      (fun j _ => heE _)
    rw [nsmul_eq_mul, hcard] at this
    simp only [hY]
    rw [← div_eq_inv_mul, div_le_iff₀ hn]; linarith
  have hYm : Measurable Y :=
    (Finset.measurable_sum _ (fun j _ => hem.comp (measurable_pi_apply j))).const_mul _
  have hlogE : Real.log E = B / (lam * eps) := Real.log_exp _
  have hlogY0 : ∀ zs, 0 ≤ Real.log (Y zs) := fun zs => Real.log_nonneg (hY1 zs)
  have hlogYE : ∀ zs, Real.log (Y zs) ≤ B / (lam * eps) := fun zs => by
    rw [← hlogE]; exact Real.log_le_log (by linarith [hY1 zs]) (hYE zs)
  -- the level-ℓ objective as an iterated integral
  have hψm : Measurable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => lam * eps * Real.log (Y ζ.2)) :=
    ((hYm.comp measurable_snd).log).const_mul _
  have hψint : Integrable (fun ζ : Z × (Fin (2 ^ ℓ) → Z) => lam * eps * Real.log (Y ζ.2))
      (levelLaw P Q (2 ^ ℓ)) := by
    refine Integrable.of_bound hψm.aestronglyMeasurable (lam * eps * (B / (lam * eps)))
      (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le (hlogY0 _))]
    exact mul_le_mul_of_nonneg_left (hlogYE _) ha.le
  have hFl : objFℓ P Q lam eps f ℓ θ
      = ∫ x, ∫ zs, lam * eps * Real.log (Y zs) ∂(Measure.pi fun _ : Fin (2 ^ ℓ) => Q x) ∂P :=
    levelLaw_integral P Q _ (fun ζ => lam * eps * Real.log (Y ζ.2)) hψm.stronglyMeasurable hψint
  have hAint := levelLaw_integrable_inner P Q _ (fun ζ => lam * eps * Real.log (Y ζ.2))
    hψm.stronglyMeasurable hψint
  -- the objective
  have hmm : Measurable (fun x => ∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x)) := by
    have : StronglyMeasurable (fun p : Z × Z => Real.exp (f θ p.2 / (lam * eps))) :=
      (hem.comp measurable_snd).stronglyMeasurable
    exact (this.integral_kernel_prod_right' (κ := Q)).measurable
  have heI : ∀ x, Integrable (fun z => Real.exp (f θ z / (lam * eps))) (Q x) := by
    intro x
    refine Integrable.of_bound hem.aestronglyMeasurable E (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact heE z
  have hm1 : ∀ x, 1 ≤ ∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x) := fun x => by
    have := integral_mono (integrable_const 1) (heI x) he1
    simpa using this
  have hmE : ∀ x, ∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x) ≤ E := fun x => by
    have := integral_mono (heI x) (integrable_const E) heE
    simpa using this
  have hBint : Integrable
      (fun x => lam * eps * Real.log (∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x))) P := by
    refine Integrable.of_bound ((hmm.log).const_mul _).aestronglyMeasurable
      (lam * eps * (B / (lam * eps))) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.le (Real.log_nonneg (hm1 x)))]
    refine mul_le_mul_of_nonneg_left ?_ ha.le
    rw [← hlogE]; exact Real.log_le_log (by linarith [hm1 x]) (hmE x)
  set C := lam * eps * Real.exp (2 * (B / (lam * eps))) * ((2 : ℝ) ^ (ℓ + 1))⁻¹ with hC
  have hpt : ∀ x, |∫ zs, lam * eps * Real.log (Y zs) ∂(Measure.pi fun _ : Fin (2 ^ ℓ) => Q x)
      - lam * eps * Real.log (∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x))| ≤ C := by
    intro x
    set μx := Measure.pi fun _ : Fin (2 ^ ℓ) => Q x with hμx
    set m := ∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x) with hm
    have hm1' := hm1 x
    have hmE' := hmE x
    have hmpos : 0 < m := by linarith
    set φ : Z → ℝ := fun z => Real.exp (f θ z / (lam * eps)) - m with hφ
    have hφm : Measurable φ := hem.sub measurable_const
    have hφ0 : ∫ z, φ z ∂(Q x) = 0 := by
      rw [hφ, integral_sub (heI x) (integrable_const _)]; simp [← hm]
    have hφR : ∀ z, |φ z| ≤ E := by
      intro z; rw [abs_le]
      have := he1 z; have := heE z
      constructor <;> simp only [hφ] <;> linarith
    have hvar := pi_var (Q x) (fun _ : Fin (2 ^ ℓ) => n⁻¹) φ hφm E hφR hφ0
    have hsq : ∑ _j : Fin (2 ^ ℓ), (n⁻¹) ^ 2 = n⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]; field_simp
    rw [hsq] at hvar
    have hYφ : ∀ zs, Y zs - m = ∑ j, n⁻¹ * φ (zs j) := by
      intro zs
      simp only [hY, hφ, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, hcard]
      field_simp
    -- Popoviciu-type bound on the variance
    have hpop : ∫ z, φ z ^ 2 ∂(Q x) ≤ ((E - 1) / 2) ^ 2 := by
      set c := (1 + E) / 2 with hc
      have hb : ∀ z, (Real.exp (f θ z / (lam * eps)) - c) ^ 2 ≤ ((E - 1) / 2) ^ 2 := by
        intro z
        rw [← sq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        rw [abs_le]; have := he1 z; have := heE z
        constructor <;> linarith
      have hId : ∀ z, φ z ^ 2 = (Real.exp (f θ z / (lam * eps)) - c) ^ 2
          - (m - c) * (2 * Real.exp (f θ z / (lam * eps)) - m - c) := fun z => by
        simp only [hφ]; ring
      have hi1 : Integrable (fun z => (Real.exp (f θ z / (lam * eps)) - c) ^ 2) (Q x) := by
        refine Integrable.of_bound ((hem.sub measurable_const).pow_const 2).aestronglyMeasurable
          (((E - 1) / 2) ^ 2) (Filter.Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb z
      have hi2 : Integrable (fun z => (m - c) * (2 * Real.exp (f θ z / (lam * eps)) - m - c))
          (Q x) := (((heI x).const_mul 2).sub (integrable_const _) |>.sub
            (integrable_const _)).const_mul _
      have i_a : Integrable (fun z => 2 * Real.exp (f θ z / (lam * eps))) (Q x) :=
        (heI x).const_mul 2
      have i_b : Integrable (fun z => 2 * Real.exp (f θ z / (lam * eps)) - m) (Q x) :=
        i_a.sub (integrable_const m)
      have hval : ∫ z, (m - c) * (2 * Real.exp (f θ z / (lam * eps)) - m - c) ∂(Q x)
          = (m - c) ^ 2 := by
        rw [integral_const_mul, integral_sub i_b (integrable_const c),
          integral_sub i_a (integrable_const m), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul, ← hm]
        ring
      calc ∫ z, φ z ^ 2 ∂(Q x)
          = ∫ z, ((Real.exp (f θ z / (lam * eps)) - c) ^ 2
              - (m - c) * (2 * Real.exp (f θ z / (lam * eps)) - m - c)) ∂(Q x) :=
            integral_congr_ae (Filter.Eventually.of_forall hId)
        _ = ∫ z, (Real.exp (f θ z / (lam * eps)) - c) ^ 2 ∂(Q x) - (m - c) ^ 2 := by
            rw [integral_sub hi1 hi2, hval]
        _ ≤ ((E - 1) / 2) ^ 2 := by
            have h1 := integral_mono hi1 (integrable_const (((E - 1) / 2) ^ 2)) hb
            simp only [integral_const, probReal_univ, one_smul] at h1
            nlinarith [sq_nonneg (m - c)]
    -- integrability on the product
    have hlogYi : Integrable (fun zs => Real.log (Y zs)) μx := by
      refine Integrable.of_bound hYm.log.aestronglyMeasurable (B / (lam * eps))
        (Filter.Eventually.of_forall fun zs => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hlogY0 zs)]; exact hlogYE zs
    have hYi : Integrable Y μx := by
      refine Integrable.of_bound hYm.aestronglyMeasurable E
        (Filter.Eventually.of_forall fun zs => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hY1 zs])]; exact hYE zs
    have hsqi : Integrable (fun zs => (Y zs - m) ^ 2) μx := by
      refine Integrable.of_bound ((hYm.sub measurable_const).pow_const 2).aestronglyMeasurable
        (E ^ 2) (Filter.Eventually.of_forall fun zs => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rw [abs_le]; have := hY1 zs; have := hYE zs
      constructor <;> linarith
    have hYint : ∫ zs, Y zs ∂μx = m := by
      show ∫ zs, n⁻¹ * ∑ j, Real.exp (f θ (zs j) / (lam * eps)) ∂μx = m
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => ?_)]
      · rw [Finset.sum_congr rfl (fun j _ =>
          pi_coord_integral (Q x) j (fun z => Real.exp (f θ z / (lam * eps))) hem)]
        rw [Finset.sum_const, nsmul_eq_mul, hcard, ← hm]; field_simp
      · exact Integrable.of_bound (hem.comp (measurable_pi_apply j)).aestronglyMeasurable E
          (Filter.Eventually.of_forall fun zs => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact heE _)
    have hvarY : ∫ zs, (Y zs - m) ^ 2 ∂μx = n⁻¹ * ∫ z, φ z ^ 2 ∂(Q x) := by
      rw [← hvar]
      exact integral_congr_ae (Filter.Eventually.of_forall fun zs => by
        show (Y zs - m) ^ 2 = _
        rw [hYφ zs])
    -- second-order bound on the log
    have hD : ∀ zs, |Real.log (Y zs) - Real.log m - (Y zs - m) / m| ≤ (Y zs - m) ^ 2 := by
      intro zs
      have hy := hY1 zs
      have hypos : 0 < Y zs := by linarith
      set u := Y zs / m with hu
      have hupos : 0 < u := div_pos hypos hmpos
      have hlogu : Real.log (Y zs) - Real.log m = Real.log u := by
        rw [hu, Real.log_div hypos.ne' hmpos.ne']
      have hum : (Y zs - m) / m = u - 1 := by rw [hu]; field_simp
      rw [hlogu, hum]
      have h1 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
      have h2 : 1 - 1 / u ≤ Real.log u := by
        have := Real.log_le_sub_one_of_pos (inv_pos.mpr hupos)
        rw [Real.log_inv] at this
        rw [one_div]; linarith
      have hmy : 1 ≤ m * Y zs := one_le_mul_of_one_le_of_one_le hm1' hy
      have h3 : (u - 1) ^ 2 / u ≤ (Y zs - m) ^ 2 := by
        have e3 : (u - 1) ^ 2 / u = (Y zs - m) ^ 2 / (m * Y zs) := by
          rw [hu]; field_simp
        rw [e3]
        exact div_le_self (sq_nonneg _) hmy
      have h4 : (u - 1) - (1 - 1 / u) = (u - 1) ^ 2 / u := by
        field_simp
      rw [abs_le]
      constructor
      · linarith [h2, h3, h4]
      · linarith [h1, sq_nonneg (Y zs - m)]
    have hDi : Integrable (fun zs => Real.log (Y zs) - Real.log m - (Y zs - m) / m) μx :=
      ((hlogYi.sub (integrable_const _)).sub ((hYi.sub (integrable_const _)).div_const _))
    have hDint : ∫ zs, (Real.log (Y zs) - Real.log m - (Y zs - m) / m) ∂μx
        = ∫ zs, Real.log (Y zs) ∂μx - Real.log m := by
      have iA : Integrable (fun zs => Real.log (Y zs) - Real.log m) μx :=
        hlogYi.sub (integrable_const _)
      have iB : Integrable (fun zs => (Y zs - m) / m) μx := (hYi.sub (integrable_const m)).div_const m
      have iK : Integrable (fun _ : Fin (2 ^ ℓ) → Z => Real.log m) μx := integrable_const _
      have iM : Integrable (fun _ : Fin (2 ^ ℓ) → Z => m) μx := integrable_const _
      rw [integral_sub iA iB, integral_sub hlogYi iK, integral_div, integral_sub hYi iM, hYint]
      simp
    have hE2 : Real.exp (2 * (B / (lam * eps))) = E ^ 2 := by
      rw [hE, sq, ← Real.exp_add]; ring_nf
    calc |∫ zs, lam * eps * Real.log (Y zs) ∂μx - lam * eps * Real.log m|
        = lam * eps * |∫ zs, (Real.log (Y zs) - Real.log m - (Y zs - m) / m) ∂μx| := by
          rw [integral_const_mul, hDint, ← mul_sub, abs_mul, abs_of_pos ha]
      _ ≤ lam * eps * ∫ zs, (Y zs - m) ^ 2 ∂μx := by
          refine mul_le_mul_of_nonneg_left ?_ ha.le
          refine (abs_integral_le_integral_abs).trans ?_
          exact integral_mono hDi.abs hsqi hD
      _ = lam * eps * (n⁻¹ * ∫ z, φ z ^ 2 ∂(Q x)) := by rw [hvarY]
      _ ≤ lam * eps * (n⁻¹ * ((E - 1) / 2) ^ 2) := by gcongr
      _ ≤ C := by
          have h5 : ((E - 1) / 2) ^ 2 ≤ E ^ 2 / 2 := by nlinarith
          have h6 : C = lam * eps * (n⁻¹ * (E ^ 2 / 2)) := by
            rw [hC, hE2, hn_def]; field_simp; ring
          rw [h6]; gcongr
  unfold objF
  rw [hFl, ← integral_sub hAint hBint]
  calc |∫ x, (∫ zs, lam * eps * Real.log (Y zs) ∂(Measure.pi fun _ : Fin (2 ^ ℓ) => Q x)
        - lam * eps * Real.log (∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x))) ∂P|
      ≤ ∫ x, |∫ zs, lam * eps * Real.log (Y zs) ∂(Measure.pi fun _ : Fin (2 ^ ℓ) => Q x)
        - lam * eps * Real.log (∫ z, Real.exp (f θ z / (lam * eps)) ∂(Q x))| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _x, C ∂P := integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall hpt)
    _ = C := by simp
