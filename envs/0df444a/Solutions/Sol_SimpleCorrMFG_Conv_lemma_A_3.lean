-- Prove2me | solution 1 for SimpleCorrMFG.Conv.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:23:47.385035+00:00
-- url     : https://prove2.me/submissions/2e677805-9d42-4931-b74a-84686169a8fb

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_RegCondDistrib

open MeasureTheory ProbabilityTheory unitInterval Filter Topology SimpleCorrMFG.Conv

section A3
variable {𝒴 𝒵 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    [TopologicalSpace 𝒵] [PolishSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]

/-- The kernel given by a measurable map into probability measures. -/
noncomputable def pmKernelOR {Ω : Type*} [MeasurableSpace Ω] (κ : Ω → ProbabilityMeasure 𝒴)
    (hκ : Measurable κ) : Kernel Ω 𝒴 :=
  ⟨fun ω => (κ ω : Measure 𝒴), measurable_subtype_coe.comp hκ⟩

instance pmKernelOR_markov {Ω : Type*} [MeasurableSpace Ω] (κ : Ω → ProbabilityMeasure 𝒴)
    (hκ : Measurable κ) : IsMarkovKernel (pmKernelOR κ hκ) :=
  ⟨fun ω => (κ ω).prop⟩

/-- The joint law `∫ κ(ω) ⊗ δ_{Z(ω)} P(dω)` on `𝒴 × 𝒵`. -/
noncomputable def jointOR {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → 𝒵)
    (κ : Ω → ProbabilityMeasure 𝒴) (hκ : Measurable κ) : Measure (𝒴 × 𝒵) :=
  (P ⊗ₘ pmKernelOR κ hκ).map (fun p => (p.2, Z p.1))

lemma jointOR_rect {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → 𝒵) (hZ : Measurable Z) (κ : Ω → ProbabilityMeasure 𝒴) (hκ : Measurable κ)
    {A : Set 𝒴} {B : Set 𝒵} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    jointOR P Z κ hκ (A ×ˢ B) = ∫⁻ ω in Z ⁻¹' B, (κ ω : Measure 𝒴) A ∂P := by
  unfold jointOR
  have hm : Measurable (fun p : Ω × 𝒴 => (p.2, Z p.1)) := measurable_snd.prodMk (hZ.comp measurable_fst)
  rw [Measure.map_apply hm (hA.prod hB)]
  have : (fun p : Ω × 𝒴 => (p.2, Z p.1)) ⁻¹' (A ×ˢ B) = (Z ⁻¹' B) ×ˢ A := by
    ext p; simp [and_comm]
  rw [this, Measure.compProd_apply_prod (hZ hB) hA]
  rfl

lemma jointOR_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → 𝒵) (hZ : Measurable Z) (κ : Ω → ProbabilityMeasure 𝒴) (hκ : Measurable κ) :
    IsProbabilityMeasure (jointOR P Z κ hκ) := by
  unfold jointOR
  have hm : Measurable (fun p : Ω × 𝒴 => (p.2, Z p.1)) := measurable_snd.prodMk (hZ.comp measurable_fst)
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

lemma jointOR_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → 𝒵) (hZ : Measurable Z) (κ : Ω → ProbabilityMeasure 𝒴) (hκ : Measurable κ)
    (f : BoundedContinuousFunction 𝒴 ℝ) (g : BoundedContinuousFunction 𝒵 ℝ) :
    ∫ p, f p.1 * g p.2 ∂(jointOR P Z κ hκ) =
      ∫ ω, (∫ y, f y ∂(κ ω : Measure 𝒴)) * g (Z ω) ∂P := by
  unfold jointOR
  have hm : Measurable (fun p : Ω × 𝒴 => (p.2, Z p.1)) := measurable_snd.prodMk (hZ.comp measurable_fst)
  have hfg : Continuous (fun p : 𝒴 × 𝒵 => f p.1 * g p.2) :=
    (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)
  rw [integral_map hm.aemeasurable hfg.aestronglyMeasurable]
  have hint : Integrable (fun p : Ω × 𝒴 => f p.2 * g (Z p.1)) (P ⊗ₘ pmKernelOR κ hκ) := by
    refine Integrable.of_bound ((hfg.measurable.comp hm).aestronglyMeasurable) (‖f‖ * ‖g‖)
      (ae_of_all _ fun p => ?_)
    rw [norm_mul]
    exact mul_le_mul (f.norm_coe_le_norm _) (g.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  rw [Measure.integral_compProd hint]
  congr 1
  funext ω
  show ∫ b, f b * g (Z ω) ∂((κ ω : Measure 𝒴)) = _
  rw [integral_mul_const]

end A3

theorem solution {𝒴 𝒵 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    [TopologicalSpace 𝒵] [PolishSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (Yn : ∀ n, Ω n → 𝒴) (Zn : ∀ n, Ω n → 𝒵) (κn : ∀ n, Ω n → ProbabilityMeasure 𝒴)
    (hYn : ∀ n, Measurable (Yn n)) (hZn : ∀ n, Measurable (Zn n)) (hκn : ∀ n, Measurable (κn n))
    (hrcd : ∀ n, IsRegCondDistrib (P n) (Yn n) (fun ω => (κn n ω : Measure 𝒴))
      (MeasurableSpace.comap (Zn n) inferInstance))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → 𝒴) (Z : Ω' → 𝒵) (κ : Ω' → ProbabilityMeasure 𝒴) (hY : Measurable Y)
    (hZ : Measurable Z) (hκ : Measurable κ)
    (hconv : ∀ g : BoundedContinuousFunction (𝒴 × 𝒵 × ProbabilityMeasure 𝒴) ℝ,
      Tendsto (fun n => ∫ ω, g (Yn n ω, Zn n ω, κn n ω) ∂(P n)) atTop
        (𝓝 (∫ ω, g (Y ω, Z ω, κ ω) ∂P'))) :
    (∀ A : Set 𝒴, MeasurableSet A → ∀ B : Set 𝒵, MeasurableSet B →
        P' (Y ⁻¹' A ∩ Z ⁻¹' B) = ∫⁻ ω in Z ⁻¹' B, (κ ω : Measure 𝒴) A ∂P') ∧
      ((∀ A : Set 𝒴, MeasurableSet A →
          Measurable[MeasurableSpace.comap Z inferInstance] (fun ω => (κ ω : Measure 𝒴) A)) →
        IsRegCondDistrib P' Y (fun ω => (κ ω : Measure 𝒴)) (MeasurableSpace.comap Z inferInstance)) := by
  -- prelimit: the joint law of `(Y_n, Z_n)` is `∫ κ_n ⊗ δ_{Z_n}`
  have hlawn : ∀ n, (P n).map (fun ω => (Yn n ω, Zn n ω)) = jointOR (P n) (Zn n) (κn n) (hκn n) := by
    intro n
    haveI := Measure.isProbabilityMeasure_map (μ := P n) ((hYn n).prodMk (hZn n)).aemeasurable
    haveI := jointOR_prob (P n) (Zn n) (hZn n) (κn n) (hκn n)
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by simp)
    rintro _ ⟨A, hA, B, hB, rfl⟩
    rw [Measure.map_apply ((hYn n).prodMk (hZn n)) (MeasurableSet.prod hA hB),
      jointOR_rect (P n) (Zn n) (hZn n) (κn n) (hκn n) hA hB]
    have := ((hrcd n).2 A hA).2 (Zn n ⁻¹' B) ⟨B, hB, rfl⟩
    rw [← this]
    rfl
  -- integrals of products of bounded continuous functions
  have hlim : ∀ (f : BoundedContinuousFunction 𝒴 ℝ) (g : BoundedContinuousFunction 𝒵 ℝ),
      ∫ ω, f (Y ω) * g (Z ω) ∂P' = ∫ ω, (∫ y, f y ∂(κ ω : Measure 𝒴)) * g (Z ω) ∂P' := by
    intro f g
    let F1 : BoundedContinuousFunction (𝒴 × 𝒵 × ProbabilityMeasure 𝒴) ℝ :=
      (f.compContinuous ⟨Prod.fst, continuous_fst⟩) *
        (g.compContinuous ⟨fun q => q.2.1, continuous_fst.comp continuous_snd⟩)
    let Iint : BoundedContinuousFunction (ProbabilityMeasure 𝒴) ℝ :=
      BoundedContinuousFunction.mkOfBound
        ⟨fun k => ∫ y, f y ∂(k : Measure 𝒴), ProbabilityMeasure.continuous_integral_boundedContinuousFunction f⟩
        (2 * ‖f‖) (fun a b => by
          simp only [ContinuousMap.coe_mk, Real.dist_eq]
          have ha : |∫ y, f y ∂(a : Measure 𝒴)| ≤ ‖f‖ := by
            rw [← Real.norm_eq_abs]
            exact (norm_integral_le_of_norm_le_const (ae_of_all _ fun y => f.norm_coe_le_norm y)).trans
              (by simp)
          have hb : |∫ y, f y ∂(b : Measure 𝒴)| ≤ ‖f‖ := by
            rw [← Real.norm_eq_abs]
            exact (norm_integral_le_of_norm_le_const (ae_of_all _ fun y => f.norm_coe_le_norm y)).trans
              (by simp)
          have := abs_sub (∫ y, f y ∂(a : Measure 𝒴)) (∫ y, f y ∂(b : Measure 𝒴))
          linarith)
    let F2 : BoundedContinuousFunction (𝒴 × 𝒵 × ProbabilityMeasure 𝒴) ℝ :=
      (Iint.compContinuous ⟨fun q => q.2.2, continuous_snd.comp continuous_snd⟩) *
        (g.compContinuous ⟨fun q => q.2.1, continuous_fst.comp continuous_snd⟩)
    have h1 := hconv F1
    have h2 := hconv F2
    have heq : ∀ n, ∫ ω, F1 (Yn n ω, Zn n ω, κn n ω) ∂(P n) = ∫ ω, F2 (Yn n ω, Zn n ω, κn n ω) ∂(P n) := by
      intro n
      have hfg : Continuous (fun p : 𝒴 × 𝒵 => f p.1 * g p.2) :=
        (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)
      have e1 : ∫ ω, F1 (Yn n ω, Zn n ω, κn n ω) ∂(P n) =
          ∫ p, f p.1 * g p.2 ∂((P n).map (fun ω => (Yn n ω, Zn n ω))) := by
        rw [integral_map ((hYn n).prodMk (hZn n)).aemeasurable hfg.aestronglyMeasurable]
        rfl
      rw [e1, hlawn n, jointOR_integral (P n) (Zn n) (hZn n) (κn n) (hκn n) f g]
      rfl
    simp_rw [heq] at h1
    have := tendsto_nhds_unique h1 h2
    exact this
  -- the limit joint law
  have hlaw : P'.map (fun ω => (Y ω, Z ω)) = jointOR P' Z κ hκ := by
    haveI := Measure.isProbabilityMeasure_map (μ := P') (hY.prodMk hZ).aemeasurable
    haveI := jointOR_prob P' Z hZ κ hκ
    refine Measure.ext_of_integral_mul_boundedContinuousFunction fun f g => ?_
    have hfg : Continuous (fun p : 𝒴 × 𝒵 => f p.1 * g p.2) :=
      (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)
    rw [integral_map (hY.prodMk hZ).aemeasurable hfg.aestronglyMeasurable,
      jointOR_integral P' Z hZ κ hκ f g]
    exact hlim f g
  have part1 : ∀ A : Set 𝒴, MeasurableSet A → ∀ B : Set 𝒵, MeasurableSet B →
      P' (Y ⁻¹' A ∩ Z ⁻¹' B) = ∫⁻ ω in Z ⁻¹' B, (κ ω : Measure 𝒴) A ∂P' := by
    intro A hA B hB
    rw [← jointOR_rect P' Z hZ κ hκ hA hB, ← hlaw, Measure.map_apply (hY.prodMk hZ) (hA.prod hB)]
    rfl
  refine ⟨part1, fun hmeas => ⟨fun ω => (κ ω).prop, fun A hA => ⟨hmeas A hA, fun s hs => ?_⟩⟩⟩
  obtain ⟨B, hB, rfl⟩ := hs
  exact part1 A hA B hB
