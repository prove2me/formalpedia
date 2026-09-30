-- Prove2me | solution 1 for UnderstandingML.compression_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T05:25:25.800472+00:00
-- url     : https://prove2.me/submissions/60a29d61-34b2-4f0c-b830-ec67aaaad293

import Definitions.Def_UnderstandingML_Compression
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory ProbabilityTheory

namespace CompressionAux

variable {Z : Type*} [MeasurableSpace Z]

lemma exp_neg_le_quad {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hx
  have hpos : 0 < Real.exp x := Real.exp_pos x
  have hq : 0 ≤ 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left h hq, sq_nonneg (x ^ 2)]

lemma integrable_of_mem_Icc (D : Measure Z) [IsProbabilityMeasure D] {f : Z → ℝ}
    (hf : Measurable f) (hf01 : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1) : Integrable f D :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf01 z).1]; exact (hf01 z).2)

/-- Moment generating function bound for a `[0,1]`-valued variable. -/
lemma integral_exp_neg_le (D : Measure Z) [IsProbabilityMeasure D] {f : Z → ℝ}
    (hf : Measurable f) (hf01 : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1) {l : ℝ} (hl : 0 ≤ l) :
    ∫ z, Real.exp (-l * f z) ∂D ≤ Real.exp (-(∫ z, f z ∂D) * (l - l ^ 2 / 2)) := by
  have hfi := integrable_of_mem_Icc D hf hf01
  -- convexity: `exp (-l x) ≤ 1 - x (1 - exp (-l))` on `[0,1]`
  have hpt : ∀ z, Real.exp (-l * f z) ≤ 1 - f z * (1 - Real.exp (-l)) := by
    intro z
    have h01 := hf01 z
    have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-l))
      (by linarith [h01.2] : (0 : ℝ) ≤ 1 - f z) h01.1 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
    have e : f z * -l = -l * f z := by ring
    rw [e] at this
    linarith
  have hμ0 : 0 ≤ ∫ z, f z ∂D := integral_nonneg fun z ↦ (hf01 z).1
  have hint : ∫ z, Real.exp (-l * f z) ∂D ≤ 1 - (∫ z, f z ∂D) * (1 - Real.exp (-l)) := by
    have hi2 : Integrable (fun z ↦ 1 - f z * (1 - Real.exp (-l))) D :=
      (integrable_const _).sub (hfi.mul_const _)
    calc ∫ z, Real.exp (-l * f z) ∂D ≤ ∫ z, (1 - f z * (1 - Real.exp (-l))) ∂D := by
          refine integral_mono_of_nonneg (ae_of_all _ fun z ↦ (Real.exp_pos _).le) hi2
            (ae_of_all _ hpt)
      _ = 1 - (∫ z, f z ∂D) * (1 - Real.exp (-l)) := by
          rw [integral_sub (integrable_const _) (hfi.mul_const _), integral_const,
            integral_mul_const]
          simp
  have hq : l - l ^ 2 / 2 ≤ 1 - Real.exp (-l) := by linarith [exp_neg_le_quad hl]
  calc ∫ z, Real.exp (-l * f z) ∂D ≤ 1 - (∫ z, f z ∂D) * (1 - Real.exp (-l)) := hint
    _ ≤ Real.exp (-((∫ z, f z ∂D) * (1 - Real.exp (-l)))) := by
        have := Real.add_one_le_exp (-((∫ z, f z ∂D) * (1 - Real.exp (-l))))
        linarith
    _ ≤ Real.exp (-(∫ z, f z ∂D) * (l - l ^ 2 / 2)) := by
        apply Real.exp_le_exp.2
        nlinarith [mul_le_mul_of_nonneg_left hq hμ0]

/-- Lower-tail multiplicative Chernoff bound for i.i.d. `[0,1]`-valued variables. -/
lemma chernoff_lower {ι : Type*} [Fintype ι] (D : Measure Z) [IsProbabilityMeasure D]
    {f : Z → ℝ} (hf : Measurable f) (hf01 : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    (hμ : 0 < ∫ z, f z ∂D) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : ι ↦ D) {S | ∑ i, f (S i) ≤ (Fintype.card ι) * ((∫ z, f z ∂D) - t)} ≤
      ENNReal.ofReal (Real.exp (-(Fintype.card ι) * t ^ 2 / (2 * ∫ z, f z ∂D))) := by
  set μ := ∫ z, f z ∂D with hμdef
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  set P := Measure.pi fun _ : ι ↦ D
  set l := t / μ with hl
  have hl0 : 0 ≤ l := div_nonneg ht hμ.le
  have hmeas : Measurable fun S : ι → Z ↦ ∑ i, f (S i) :=
    Finset.measurable_sum _ fun i _ ↦ hf.comp (measurable_pi_apply i)
  have hbound : ∀ S : ι → Z, Real.exp (-l * ∑ i, f (S i)) = ∏ i, Real.exp (-l * f (S i)) := by
    intro S; rw [Finset.mul_sum, Real.exp_sum]
  have hint : Integrable (fun S : ι → Z ↦ Real.exp (-l * ∑ i, f (S i))) P := by
    refine (integrable_const (1 : ℝ)).mono'
      ((Real.continuous_exp.measurable.comp (hmeas.const_mul _)).aestronglyMeasurable)
      (ae_of_all _ fun S ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have : 0 ≤ ∑ i, f (S i) := Finset.sum_nonneg fun i _ ↦ (hf01 _).1
    nlinarith
  have hmgf : mgf (fun S : ι → Z ↦ ∑ i, f (S i)) P (-l) ≤
      Real.exp (-μ * (l - l ^ 2 / 2)) ^ (Fintype.card ι) := by
    unfold mgf
    simp_rw [hbound]
    rw [integral_fintype_prod_eq_prod (fun _ z ↦ Real.exp (-l * f z))]
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun i _ ↦ integral_nonneg fun z ↦ (Real.exp_pos _).le)
      fun i _ ↦ integral_exp_neg_le D hf hf01 hl0
  have hmain := measure_le_le_exp_mul_mgf (X := fun S : ι → Z ↦ ∑ i, f (S i)) (μ := P)
    (n * (μ - t)) (by linarith : -l ≤ 0) hint
  have hreal : P.real {S | ∑ i, f (S i) ≤ n * (μ - t)} ≤
      Real.exp (-n * t ^ 2 / (2 * μ)) := by
    refine hmain.trans ?_
    calc Real.exp (- -l * (n * (μ - t))) * mgf (fun S : ι → Z ↦ ∑ i, f (S i)) P (-l)
        ≤ Real.exp (- -l * (n * (μ - t))) * Real.exp (-μ * (l - l ^ 2 / 2)) ^ (Fintype.card ι) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = Real.exp (-n * t ^ 2 / (2 * μ)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          rw [hl]
          field_simp
          ring
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The deterministic step of Lemma 30.1: solving the quadratic in `√L_D`. -/
lemma sqrt_step {μ x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a)
    (h : Real.sqrt (2 * x * a) + 4 * a ≤ μ - x) :
    0 < μ ∧ x ≤ μ - Real.sqrt (2 * μ * a) := by
  set r := Real.sqrt (2 * x * a) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 2 * x * a := Real.sq_sqrt (by positivity)
  have hμ : 0 < μ := by linarith
  refine ⟨hμ, ?_⟩
  have hd : r + 4 * a ≤ μ - x := h
  have key : 2 * μ * a ≤ (μ - x) ^ 2 := by
    nlinarith [mul_le_mul hd hd (by positivity) (by linarith)]
  have := Real.sqrt_le_sqrt key
  rw [Real.sqrt_sq (by linarith)] at this
  linarith

/-- The held-out Bernstein-type bound for a fixed hypothesis evaluated on `n` fresh examples. -/
lemma holdout_fixed {ι : Type*} [Fintype ι] [Nonempty ι] (D : Measure Z) [IsProbabilityMeasure D]
    {f : Z → ℝ} (hf : Measurable f) (hf01 : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : ι ↦ D) {S | Real.sqrt (2 * ((∑ i, f (S i)) / Fintype.card ι) *
        Real.log (1 / δ) / Fintype.card ι) + 4 * Real.log (1 / δ) / Fintype.card ι ≤
        (∫ z, f z ∂D) - (∑ i, f (S i)) / Fintype.card ι} ≤ ENNReal.ofReal δ := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set L := Real.log (1 / δ) with hL
  have hL0 : 0 < L := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hδ, hδ1⟩)
  set a := L / n with ha
  have ha0 : 0 < a := div_pos hL0 hn0
  by_cases hμ : 0 < ∫ z, f z ∂D
  · set μ := ∫ z, f z ∂D
    refine le_trans (measure_mono ?_) ((chernoff_lower (ι := ι) D hf hf01 hμ
      (Real.sqrt_nonneg (2 * μ * a))).trans ?_)
    · intro S hS
      simp only [Set.mem_setOf_eq] at hS ⊢
      have hx : 0 ≤ (∑ i, f (S i)) / n :=
        div_nonneg (Finset.sum_nonneg fun i _ ↦ (hf01 _).1) hn0.le
      have e1 : 2 * ((∑ i, f (S i)) / n) * L / n = 2 * ((∑ i, f (S i)) / n) * a := by
        rw [ha]; ring
      have e2 : 4 * L / n = 4 * a := by rw [ha]; ring
      rw [e1, e2] at hS
      have := (sqrt_step hx ha0 hS).2
      have h2 : (∑ i, f (S i)) = n * ((∑ i, f (S i)) / n) := by field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left this hn0.le
    · apply ENNReal.ofReal_le_ofReal
      rw [Real.sq_sqrt (by positivity)]
      have : -n * (2 * μ * a) / (2 * μ) = -L := by
        rw [ha]; field_simp
      rw [this, hL, Real.log_div one_ne_zero hδ.ne', Real.log_one, zero_sub, neg_neg,
        Real.exp_log hδ]
  · push_neg at hμ
    refine le_of_eq_of_le (b := 0) ?_ (by simp)
    rw [measure_eq_zero_iff_ae_notMem]
    refine ae_of_all _ fun S hS ↦ ?_
    simp only [Set.mem_setOf_eq] at hS
    have hx : 0 ≤ (∑ i, f (S i)) / n :=
      div_nonneg (Finset.sum_nonneg fun i _ ↦ (hf01 _).1) hn0.le
    have h4 : 0 < 4 * L / n := by positivity
    have := Real.sqrt_nonneg (2 * ((∑ i, f (S i)) / n) * L / n)
    linarith

/-- A product measure bound from uniform bounds on the sections. -/
lemma prod_le_of_section {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [SFinite ν]
    {E : Set (α × β)} (hE : MeasurableSet E) {ε : ENNReal}
    (h : ∀ a, ν (Prod.mk a ⁻¹' E) ≤ ε) : μ.prod ν E ≤ ε := by
  rw [Measure.prod_apply hE]
  calc ∫⁻ a, ν (Prod.mk a ⁻¹' E) ∂μ ≤ ∫⁻ _, ε ∂μ := lintegral_mono h
    _ = ε := by simp

/-- The held-out bound when the hypothesis is built from the coordinates in `p` and evaluated on
the coordinates outside `p`. -/
lemma holdout_split {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    [Nonempty {i // ¬ p i}] (D : Measure Z) [IsProbabilityMeasure D]
    (H : ({i // p i} → Z) → Z → ℝ)
    (hH : Measurable (fun q : ({i // p i} → Z) × Z ↦ H q.1 q.2))
    (hH01 : ∀ a z, H a z ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : ι ↦ D) {S |
        Real.sqrt (2 * ((∑ i : {i // ¬ p i}, H (fun j ↦ S j) (S i)) /
          Fintype.card {i // ¬ p i}) * Real.log (1 / δ) / Fintype.card {i // ¬ p i}) +
          4 * Real.log (1 / δ) / Fintype.card {i // ¬ p i} ≤
        (∫ z, H (fun j ↦ S j) z ∂D) -
          (∑ i : {i // ¬ p i}, H (fun j ↦ S j) (S i)) / Fintype.card {i // ¬ p i}} ≤
      ENNReal.ofReal δ := by
  set c : ℝ := (Fintype.card {i // ¬ p i} : ℝ)
  set L := Real.log (1 / δ)
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι ↦ D) p
  set E' : Set (({i // p i} → Z) × ({i // ¬ p i} → Z)) := {q |
    Real.sqrt (2 * ((∑ i, H q.1 (q.2 i)) / c) * L / c) + 4 * L / c ≤
      (∫ z, H q.1 z ∂D) - (∑ i, H q.1 (q.2 i)) / c} with hE'def
  have hsum : Measurable fun q : ({i // p i} → Z) × ({i // ¬ p i} → Z) ↦ ∑ i, H q.1 (q.2 i) :=
    Finset.measurable_sum _ fun i _ ↦
      hH.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hint : Measurable fun q : ({i // p i} → Z) × ({i // ¬ p i} → Z) ↦ ∫ z, H q.1 z ∂D :=
    (hH.stronglyMeasurable.integral_prod_right' (ν := D)).measurable.comp measurable_fst
  have hE' : MeasurableSet E' := by
    refine measurableSet_le ?_ ?_
    · exact (Real.continuous_sqrt.measurable.comp
        ((((hsum.div_const c).const_mul 2).mul_const L).div_const c)).add measurable_const
    · exact hint.sub (hsum.div_const c)
  have hset : {S : ι → Z |
        Real.sqrt (2 * ((∑ i : {i // ¬ p i}, H (fun j ↦ S j) (S i)) /
          Fintype.card {i // ¬ p i}) * Real.log (1 / δ) / Fintype.card {i // ¬ p i}) +
          4 * Real.log (1 / δ) / Fintype.card {i // ¬ p i} ≤
        (∫ z, H (fun j ↦ S j) z ∂D) -
          (∑ i : {i // ¬ p i}, H (fun j ↦ S j) (S i)) / Fintype.card {i // ¬ p i}} =
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι ↦ Z) p) ⁻¹' E' := rfl
  rw [hset, hmp.measure_preimage hE'.nullMeasurableSet]
  refine prod_le_of_section _ _ hE' fun a ↦ ?_
  exact holdout_fixed D (hH.comp (measurable_const.prodMk measurable_id)) (hH01 a) hδ hδ1

end CompressionAux


open MeasureTheory
open scoped InnerProductSpace

open UnderstandingML CompressionAux in
theorem solution {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (k m : ℕ) (hk : 1 ≤ k) (hm : 2 * k ≤ m) (hm0 : 0 < m) (B : (Fin k → Z) → Hyp)
    (hB : Measurable (fun p : (Fin k → Z) × Z ↦ loss (B p.1) p.2))
    (sel : (Fin m → Z) → Fin k → Fin m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw D m {S | heldOutRisk loss sel S (compressedHyp B sel S) +
        Real.sqrt (heldOutRisk loss sel S (compressedHyp B sel S) * 4 * k * Real.log (m / δ) / m) +
        8 * k * Real.log (m / δ) / m < risk loss D (compressedHyp B sel S)} ≤
      ENNReal.ofReal δ := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmk : (1 : ℝ) ≤ (m : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hm0)
  set δ' : ℝ := δ / (m : ℝ) ^ k with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ (by positivity)
  have hδ'1 : δ' < 1 := lt_of_le_of_lt (div_le_self hδ.le hmk) hδ1
  -- the events for a fixed index sequence `I`
  let p : (Fin k → Fin m) → Fin m → Prop := fun I i ↦ ∃ j, I j = i
  let H : (I : Fin k → Fin m) → ({i // p I i} → Z) → Z → ℝ :=
    fun I a z ↦ loss (B (fun j ↦ a ⟨I j, j, rfl⟩)) z
  have hcardV : ∀ I, (m : ℝ) - k ≤ Fintype.card {i // ¬ p I i} := by
    intro I
    have h1 : Fintype.card {i // p I i} ≤ k := by
      have := Fintype.card_le_of_surjective (fun j : Fin k ↦ (⟨I j, j, rfl⟩ : {i // p I i}))
        (by rintro ⟨i, j, rfl⟩; exact ⟨j, rfl⟩)
      simpa using this
    have h2 := Fintype.card_subtype_compl (p I)
    rw [Fintype.card_fin] at h2
    have h3 : Fintype.card {i // p I i} ≤ m := by
      have := Fintype.card_subtype_le (p I); simpa using this
    rw [h2, Nat.cast_sub h3]
    have : (Fintype.card {i // p I i} : ℝ) ≤ k := by exact_mod_cast h1
    linarith
  have hVpos : ∀ I, (m : ℝ) / 2 ≤ Fintype.card {i // ¬ p I i} := by
    intro I
    have : (2 * k : ℝ) ≤ m := by exact_mod_cast hm
    linarith [hcardV I]
  have hVne : ∀ I, Nonempty {i // ¬ p I i} := by
    intro I
    have : 0 < Fintype.card {i // ¬ p I i} := by
      have := hVpos I
      exact_mod_cast (show (0 : ℝ) < Fintype.card {i // ¬ p I i} by linarith)
    exact Fintype.card_pos_iff.1 this
  let E : (Fin k → Fin m) → Set (Fin m → Z) := fun I ↦ {S |
      Real.sqrt (2 * ((∑ i : {i // ¬ p I i}, H I (fun j ↦ S j) (S i)) /
        Fintype.card {i // ¬ p I i}) * Real.log (1 / δ') / Fintype.card {i // ¬ p I i}) +
        4 * Real.log (1 / δ') / Fintype.card {i // ¬ p I i} ≤
      (∫ z, H I (fun j ↦ S j) z ∂D) -
        (∑ i : {i // ¬ p I i}, H I (fun j ↦ S j) (S i)) / Fintype.card {i // ¬ p I i}}
  have hE : ∀ I, iidLaw D m (E I) ≤ ENNReal.ofReal δ' := by
    intro I
    haveI := hVne I
    have hg : Measurable (fun q : ({i // p I i} → Z) × Z ↦
        ((fun j ↦ q.1 ⟨I j, j, rfl⟩ : Fin k → Z), q.2)) :=
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd
    exact holdout_split (p I) D (H I) (hB.comp hg) (fun a z ↦ hloss _ z) hδ'0 hδ'1
  -- logarithms
  set Lm := Real.log (m / δ) with hLm
  set L' := Real.log (1 / δ') with hL'
  have hlogδ : Real.log δ < 0 := Real.log_neg hδ hδ1
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm0)
  have hL'eq : L' = k * Real.log m - Real.log δ := by
    rw [hL', hδ', one_div_div, Real.log_div (by positivity) hδ.ne', Real.log_pow]
  have hLmeq : Lm = Real.log m - Real.log δ := Real.log_div hmR.ne' hδ.ne'
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL'0 : 0 ≤ L' := by rw [hL'eq]; nlinarith
  have hL'le : L' ≤ k * Lm := by rw [hL'eq, hLmeq]; nlinarith
  -- every bad sample lies in the event of its own index sequence
  have hsub : {S | heldOutRisk loss sel S (compressedHyp B sel S) +
        Real.sqrt (heldOutRisk loss sel S (compressedHyp B sel S) * 4 * k * Lm / m) +
        8 * k * Lm / m < risk loss D (compressedHyp B sel S)} ⊆ ⋃ I, E I := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS
    refine Set.mem_iUnion.2 ⟨sel S, ?_⟩
    set I := sel S with hI
    have hmemiff : ∀ i, i ∈ unselected sel S ↔ ¬ p I i := by
      intro i; simp [unselected, p, hI]
    have hsum : (∑ i ∈ unselected sel S, loss (compressedHyp B sel S) (S i)) =
        ∑ i : {i // ¬ p I i}, H I (fun j ↦ S j) (S i) :=
      Finset.sum_subtype _ hmemiff _
    have hcard : (unselected sel S).card = Fintype.card {i // ¬ p I i} :=
      (Fintype.card_of_subtype _ hmemiff).symm
    have hheld : heldOutRisk loss sel S (compressedHyp B sel S) =
        (∑ i : {i // ¬ p I i}, H I (fun j ↦ S j) (S i)) / Fintype.card {i // ¬ p I i} := by
      unfold heldOutRisk; rw [hsum, hcard]
    have hrisk : risk loss D (compressedHyp B sel S) = ∫ z, H I (fun j ↦ S j) z ∂D := rfl
    rw [hheld, hrisk] at hS
    simp only [E, Set.mem_setOf_eq]
    set x := (∑ i : {i // ¬ p I i}, H I (fun j ↦ S j) (S i)) / Fintype.card {i // ¬ p I i}
    set n : ℝ := (Fintype.card {i // ¬ p I i} : ℝ)
    have hn : m / 2 ≤ n := hVpos I
    have hn0 : 0 < n := by linarith
    have hx0 : 0 ≤ x := div_nonneg (Finset.sum_nonneg fun i _ ↦ (hloss _ _).1) hn0.le
    have hratio : L' / n ≤ 2 * k * Lm / m := by
      rw [div_le_div_iff₀ hn0 hmR]
      have hkLm : 0 ≤ k * Lm := le_trans hL'0 hL'le
      nlinarith
    have h1 : 2 * x * L' / n ≤ x * 4 * k * Lm / m := by
      have : 2 * x * L' / n = 2 * x * (L' / n) := by ring
      rw [this]
      have : x * 4 * k * Lm / m = 2 * x * (2 * k * Lm / m) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hratio (by linarith)
    have h2 : 4 * L' / n ≤ 8 * k * Lm / m := by
      have : 4 * L' / n = 4 * (L' / n) := by ring
      rw [this]
      have : 8 * k * Lm / m = 4 * (2 * k * Lm / m) := by ring
      rw [this]
      linarith
    have h3 := Real.sqrt_le_sqrt h1
    linarith
  calc iidLaw D m _ ≤ iidLaw D m (⋃ I, E I) := measure_mono hsub
    _ ≤ ∑ I, iidLaw D m (E I) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _I : Fin k → Fin m, ENNReal.ofReal δ' := Finset.sum_le_sum fun I _ ↦ hE I
    _ = ENNReal.ofReal δ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hδ']
      push_cast
      field_simp
