-- Prove2me | solution 1 for SupportVectorMachines.Regression.theorem_A_8_1_symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:18:43.252022+00:00
-- url     : https://prove2.me/submissions/15d07cce-3c71-45df-aee1-f2d28fa633a6

import Mathlib
import Definitions.Def_SupportVectorMachines_Regression_IsRademacherSequence

open MeasureTheory ProbabilityTheory TopologicalSpace

namespace SupportVectorMachines.Regression

lemma aux_sym81_cont (Ψ : ℝ → ℝ) (hΨconv : ConvexOn ℝ (Set.Ici 0) Ψ)
    (hΨmono : MonotoneOn Ψ (Set.Ici 0)) : ContinuousOn Ψ (Set.Ici 0) := by
  refine hΨconv.continuousOn_Ici ?_
  have hup : Filter.Tendsto (fun x : ℝ => (1 - x) * Ψ 0 + x * Ψ 1)
      (nhdsWithin 0 (Set.Ici 0)) (nhds (Ψ 0)) := by
    have hc : Continuous (fun x : ℝ => (1 - x) * Ψ 0 + x * Ψ 1) := by fun_prop
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ici (0:ℝ)))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact hΨmono (show (0:ℝ) ∈ Set.Ici 0 from le_refl (0:ℝ)) hx hx
  · have h1 : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ici 0) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, h1] with x hx hx1
    have hx1' : x < 1 := hx1
    have hx0 : (0:ℝ) ≤ x := hx
    have := hΨconv.2 ((show (0:ℝ) ∈ Set.Ici 0 from le_refl (0:ℝ))) (show (1:ℝ) ∈ Set.Ici 0 by simp)
      (show (0:ℝ) ≤ 1 - x by linarith) hx0 (by ring)
    simpa [smul_eq_mul] using this

lemma aux_sym81_jensen (Ψ : ℝ → ℝ) (hΨconv : ConvexOn ℝ (Set.Ici 0) Ψ)
    (hΨmono : MonotoneOn Ψ (Set.Ici 0)) (hΨnn : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ Ψ x)
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (g : α → ℝ) (hg0 : ∀ a, 0 ≤ g a) (hgi : Integrable g μ)
    (hgm : AEStronglyMeasurable (fun a => Ψ (g a)) μ) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : t ≤ ∫ a, g a ∂μ) :
    ENNReal.ofReal (Ψ t) ≤ ∫⁻ a, ENNReal.ofReal (Ψ (g a)) ∂μ := by
  have hnn : 0 ≤ᵐ[μ] (fun a => Ψ (g a)) :=
    Filter.Eventually.of_forall (fun a => hΨnn _ (hg0 a))
  by_cases hint : Integrable (fun a => Ψ (g a)) μ
  · have hj : Ψ (∫ a, g a ∂μ) ≤ ∫ a, Ψ (g a) ∂μ :=
      hΨconv.map_integral_le (aux_sym81_cont Ψ hΨconv hΨmono) isClosed_Ici
        (Filter.Eventually.of_forall (fun a => hg0 a)) hgi hint
    have hmono : Ψ t ≤ Ψ (∫ a, g a ∂μ) :=
      hΨmono ht0 (show (0:ℝ) ≤ ∫ a, g a ∂μ from integral_nonneg hg0) ht
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_le_ofReal (hmono.trans hj)
  · have htop : ∫⁻ a, ENNReal.ofReal (Ψ (g a)) ∂μ = ⊤ := by
      by_contra hne
      apply hint
      refine ⟨hgm, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal hnn]
      exact lt_top_iff_ne_top.2 hne
    rw [htop]
    exact le_top

lemma aux_sym81_key (Ψ : ℝ → ℝ) (hΨconv : ConvexOn ℝ (Set.Ici 0) Ψ)
    (hΨmono : MonotoneOn Ψ (Set.Ici 0))
    (hΨnn : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ Ψ x) (hΨmeas : Measurable Ψ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SeparableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (ξ : Fin n → Ω → E) (hξmeas : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ P) (hξint : ∀ i, Integrable (ξ i) P) (c : ℝ)
    (s : Fin n → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    ∫⁻ ω, ENNReal.ofReal (Ψ ‖c • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖) ∂P ≤
      ∫⁻ ω, ENNReal.ofReal (Ψ (2 * ‖c • ∑ i, s i • ξ i ω‖)) ∂P := by
  let ξv : Ω → (Fin n → E) := fun ω i => ξ i ω
  have hξv : Measurable ξv := measurable_pi_lambda _ hξmeas
  have hLpi : P.map ξv = Measure.pi (fun i => P.map (ξ i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hξmeas i).aemeasurable)).1 hξindep
  have : IsProbabilityMeasure (P.map ξv) := Measure.isProbabilityMeasure_map hξv.aemeasurable
  have : ∀ i, IsProbabilityMeasure (P.map (ξ i)) :=
    fun i => Measure.isProbabilityMeasure_map (hξmeas i).aemeasurable
  let H : (Fin n → E) × (Fin n → E) → ENNReal :=
    fun q => ENNReal.ofReal (Ψ ‖c • ∑ i, (q.1 i - q.2 i)‖)
  let A : (Fin n → E) → ENNReal :=
    fun x => ENNReal.ofReal (Ψ (2 * ‖c • ∑ i, s i • x i‖))
  have hHm : Measurable H := by
    apply ENNReal.measurable_ofReal.comp
    apply hΨmeas.comp
    apply Measurable.norm
    apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp measurable_fst).sub
      ((measurable_pi_apply i).comp measurable_snd)
  have hAm : Measurable A := by
    apply ENNReal.measurable_ofReal.comp
    apply hΨmeas.comp
    apply Measurable.const_mul
    apply Measurable.norm
    apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i _
    exact (measurable_pi_apply i).const_smul _
  -- Step 1: Jensen
  have step1 : ∀ ω, ENNReal.ofReal (Ψ ‖c • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖) ≤
      ∫⁻ ω', H (ξv ω, ξv ω') ∂P := by
    intro ω
    have hint : Integrable (fun ω' => c • ∑ i, (ξ i ω - ξ i ω')) P := by
      refine Integrable.smul c ?_
      exact integrable_finsetSum _ (fun i _ => (integrable_const _).sub (hξint i))
    refine aux_sym81_jensen Ψ hΨconv hΨmono hΨnn P
      (fun ω' => ‖c • ∑ i, (ξ i ω - ξ i ω')‖) (fun _ => norm_nonneg _) hint.norm ?_ _
      (norm_nonneg _) ?_
    · have hm : Measurable (fun ω' => Ψ ‖c • ∑ i, (ξ i ω - ξ i ω')‖) := by
        apply hΨmeas.comp
        apply Measurable.norm
        apply Measurable.const_smul
        apply Finset.measurable_sum
        intro i _
        exact measurable_const.sub (hξmeas i)
      exact hm.aestronglyMeasurable
    · have heq : c • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P) = ∫ ω', c • ∑ i, (ξ i ω - ξ i ω') ∂P := by
        rw [integral_smul, integral_finsetSum]
        · congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [integral_sub (integrable_const _) (hξint i), integral_const]
          simp
        · intro i _
          exact (integrable_const _).sub (hξint i)
      rw [heq]
      exact norm_integral_le_integral_norm _
  -- Step 2: rewrite as a product integral over the laws
  have step2 : ∫⁻ ω, ∫⁻ ω', H (ξv ω, ξv ω') ∂P ∂P =
      ∫⁻ q, H q ∂((P.map ξv).prod (P.map ξv)) := by
    rw [Measure.map_prod_map P P hξv hξv, lintegral_map hHm (hξv.prodMap hξv)]
    exact (lintegral_prod _ (hHm.comp (hξv.prodMap hξv)).aemeasurable).symm
  -- Step 3: sign flip invariance
  classical
  let f : Fin n → E × E → E × E := fun i p => if s i = 1 then p else p.swap
  let F := MeasurableEquiv.arrowProdEquivProdArrow E E (Fin n)
  let T : (Fin n → E) × (Fin n → E) → (Fin n → E) × (Fin n → E) :=
    F ∘ (fun a i => f i (a i)) ∘ F.symm
  have hT : MeasurePreserving T ((P.map ξv).prod (P.map ξv)) ((P.map ξv).prod (P.map ξv)) := by
    rw [hLpi]
    have hF := measurePreserving_arrowProdEquivProdArrow E E (Fin n)
      (fun i => P.map (ξ i)) (fun i => P.map (ξ i))
    have hf : ∀ i, MeasurePreserving (f i) ((P.map (ξ i)).prod (P.map (ξ i)))
        ((P.map (ξ i)).prod (P.map (ξ i))) := by
      intro i
      by_cases h : s i = 1
      · have : f i = id := by
          funext p
          simp [f, h]
        rw [this]
        exact MeasurePreserving.id _
      · have : f i = Prod.swap := by
          funext p
          simp [f, h]
        rw [this]
        exact Measure.measurePreserving_swap
    have hσ := measurePreserving_pi _ _ hf
    exact hF.comp (hσ.comp (MeasurePreserving.symm F hF))
  have hTdiff : ∀ q i, (T q).1 i - (T q).2 i = s i • (q.1 i - q.2 i) := by
    intro q i
    rcases hs i with h | h
    · simp [T, F, f, h, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    · have hne : (-1:ℝ) ≠ 1 := by norm_num
      simp [T, F, f, h, hne, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
  have step3 : ∫⁻ q, H q ∂((P.map ξv).prod (P.map ξv)) =
      ∫⁻ q, H (T q) ∂((P.map ξv).prod (P.map ξv)) :=
    (hT.lintegral_comp hHm).symm
  -- Step 4: pointwise bound
  have step4 : ∀ q, 2 * H (T q) ≤ A q.1 + A q.2 := by
    intro q
    have hsum : c • ∑ i, ((T q).1 i - (T q).2 i) =
        c • ∑ i, s i • q.1 i - c • ∑ i, s i • q.2 i := by
      simp_rw [hTdiff, smul_sub, Finset.sum_sub_distrib, smul_sub]
    set a := ‖c • ∑ i, s i • q.1 i‖ with ha
    set b := ‖c • ∑ i, s i • q.2 i‖ with hb
    have ha0 : 0 ≤ a := norm_nonneg _
    have hb0 : 0 ≤ b := norm_nonneg _
    have hnorm : ‖c • ∑ i, ((T q).1 i - (T q).2 i)‖ ≤ a + b := by
      rw [hsum]
      exact norm_sub_le _ _
    have h1 : Ψ ‖c • ∑ i, ((T q).1 i - (T q).2 i)‖ ≤ Ψ (a + b) :=
      hΨmono (norm_nonneg _) (show (0:ℝ) ≤ a + b by linarith) hnorm
    have h2 : Ψ (a + b) ≤ (1/2) * Ψ (2 * a) + (1/2) * Ψ (2 * b) := by
      have := hΨconv.2 (show 2 * a ∈ Set.Ici (0:ℝ) from by simp; linarith)
        (show 2 * b ∈ Set.Ici (0:ℝ) from by simp; linarith)
        (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
      simp only [smul_eq_mul] at this
      have e : (1/2:ℝ) * (2*a) + 1/2 * (2*b) = a + b := by ring
      rw [e] at this
      exact this
    have hΨa : 0 ≤ Ψ (2 * a) := hΨnn _ (show (0:ℝ) ≤ 2 * a by linarith)
    have hΨb : 0 ≤ Ψ (2 * b) := hΨnn _ (show (0:ℝ) ≤ 2 * b by linarith)
    have key : 2 * Ψ ‖c • ∑ i, ((T q).1 i - (T q).2 i)‖ ≤ Ψ (2 * a) + Ψ (2 * b) := by
      linarith
    show 2 * ENNReal.ofReal (Ψ ‖c • ∑ i, ((T q).1 i - (T q).2 i)‖) ≤
      ENNReal.ofReal (Ψ (2 * a)) + ENNReal.ofReal (Ψ (2 * b))
    rw [← ENNReal.ofReal_add hΨa hΨb, show (2 : ENNReal) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal key
  -- Step 5: integrate the bound
  have step5 : ∫⁻ q, (A q.1 + A q.2) ∂((P.map ξv).prod (P.map ξv)) =
      2 * ∫⁻ x, A x ∂(P.map ξv) := by
    have e1 : ∫⁻ q, (A q.1 + A q.2) ∂((P.map ξv).prod (P.map ξv)) =
        ∫⁻ q, A q.1 ∂((P.map ξv).prod (P.map ξv)) + ∫⁻ q, A q.2 ∂((P.map ξv).prod (P.map ξv)) :=
      lintegral_add_left (hAm.comp measurable_fst) _
    have e2 : ∫⁻ q, A q.1 ∂((P.map ξv).prod (P.map ξv)) = ∫⁻ x, A x ∂(P.map ξv) := by
      refine (lintegral_prod _ (hAm.comp measurable_fst).aemeasurable).trans ?_
      simp [lintegral_const]
    have e3 : ∫⁻ q, A q.2 ∂((P.map ξv).prod (P.map ξv)) = ∫⁻ x, A x ∂(P.map ξv) := by
      refine (lintegral_prod _ (hAm.comp measurable_snd).aemeasurable).trans ?_
      simp [lintegral_const]
    rw [e1, e2, e3, two_mul]
  have step6 : ∫⁻ x, A x ∂(P.map ξv) = ∫⁻ ω, ENNReal.ofReal (Ψ (2 * ‖c • ∑ i, s i • ξ i ω‖)) ∂P := by
    rw [lintegral_map hAm hξv]
  -- Combine
  have hmain : 2 * ∫⁻ ω, ENNReal.ofReal (Ψ ‖c • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖) ∂P ≤
      2 * ∫⁻ ω, ENNReal.ofReal (Ψ (2 * ‖c • ∑ i, s i • ξ i ω‖)) ∂P := by
    calc 2 * ∫⁻ ω, ENNReal.ofReal (Ψ ‖c • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖) ∂P
        ≤ 2 * ∫⁻ ω, ∫⁻ ω', H (ξv ω, ξv ω') ∂P ∂P := by
          gcongr with ω
          exact step1 ω
      _ = 2 * ∫⁻ q, H (T q) ∂((P.map ξv).prod (P.map ξv)) := by rw [step2, step3]
      _ = ∫⁻ q, 2 * H (T q) ∂((P.map ξv).prod (P.map ξv)) := by
          exact (lintegral_const_mul 2 (hHm.comp hT.measurable)).symm
      _ ≤ ∫⁻ q, (A q.1 + A q.2) ∂((P.map ξv).prod (P.map ξv)) := lintegral_mono step4
      _ = 2 * ∫⁻ ω, ENNReal.ofReal (Ψ (2 * ‖c • ∑ i, s i • ξ i ω‖)) ∂P := by
          rw [step5, step6]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 hmain

end SupportVectorMachines.Regression

open SupportVectorMachines.Regression

theorem solution
    (Ψ : ℝ → ℝ) (hΨconv : ConvexOn ℝ (Set.Ici 0) Ψ) (hΨmono : MonotoneOn Ψ (Set.Ici 0))
    (hΨnn : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ Ψ x) (hΨmeas : Measurable Ψ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SeparableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (ξ : Fin n → Ω → E) (hξmeas : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ P) (hξident : ∀ i j, IdentDistrib (ξ i) (ξ j) P P)
    (hξint : ∀ i, Integrable (ξ i) P)
    {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    (ε : Fin n → Θ → ℝ) (hε : IsRademacherSequence ε ν) :
    ∫⁻ ω, ENNReal.ofReal (Ψ ‖(n : ℝ)⁻¹ • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖) ∂P ≤
      ∫⁻ ω, ∫⁻ θ, ENNReal.ofReal (Ψ (2 * ‖(n : ℝ)⁻¹ • ∑ i, ε i θ • ξ i ω‖)) ∂ν ∂P := by
  obtain ⟨hεm, -, hεp⟩ := hε
  have hmeas : Measurable (Function.uncurry fun (ω : Ω) (θ : Θ) =>
      ENNReal.ofReal (Ψ (2 * ‖(n : ℝ)⁻¹ • ∑ i, ε i θ • ξ i ω‖))) := by
    apply ENNReal.measurable_ofReal.comp
    apply hΨmeas.comp
    apply Measurable.const_mul
    apply Measurable.norm
    apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i _
    exact ((hεm i).comp measurable_snd).smul ((hξmeas i).comp measurable_fst)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hae : ∀ᵐ θ ∂ν, ∀ i, ε i θ = 1 ∨ ε i θ = -1 := by
    rw [ae_all_iff]
    intro i
    have hS1 : MeasurableSet {θ | ε i θ = 1} := (hεm i) (measurableSet_singleton 1)
    have hS2 : MeasurableSet {θ | ε i θ = -1} := (hεm i) (measurableSet_singleton (-1))
    have hdisj : Disjoint {θ | ε i θ = 1} {θ | ε i θ = -1} := by
      rw [Set.disjoint_left]
      intro θ h1 h2
      simp only [Set.mem_ofPred_eq] at h1 h2
      rw [h1] at h2
      norm_num at h2
    have hU : {θ | ε i θ = 1 ∨ ε i θ = -1} = {θ | ε i θ = 1} ∪ {θ | ε i θ = -1} := rfl
    rw [ae_iff_measure_eq (by rw [hU]; exact (hS1.union hS2).nullMeasurableSet), hU,
      measure_union hdisj hS2, (hεp i).1, (hεp i).2, ENNReal.add_halves, measure_univ]
  calc ∫⁻ ω, ENNReal.ofReal (Ψ ‖(n : ℝ)⁻¹ • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖) ∂P
      = ∫⁻ θ, (∫⁻ ω, ENNReal.ofReal (Ψ ‖(n : ℝ)⁻¹ • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖) ∂P) ∂ν := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ θ, ∫⁻ ω, ENNReal.ofReal (Ψ (2 * ‖(n : ℝ)⁻¹ • ∑ i, ε i θ • ξ i ω‖)) ∂P ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with θ hθ
        exact aux_sym81_key Ψ hΨconv hΨmono hΨnn hΨmeas P ξ hξmeas hξindep hξint
          ((n : ℝ)⁻¹) (fun i => ε i θ) hθ
