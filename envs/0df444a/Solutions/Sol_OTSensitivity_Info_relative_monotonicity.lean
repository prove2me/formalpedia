-- Prove2me | solution 1 for OTSensitivity.Info.relative_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:50:49.12779+00:00
-- url     : https://prove2.me/submissions/0cbfdf6f-2c4b-4d54-9239-93e90674b929

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting
import Theorems.Thm_OTSensitivity_Info_transportCost_lsc
import Theorems.Thm_OTSensitivity_Info_mixture_convexity

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTInfra

/-- A countable family of weakly continuous coordinates that determines weak convergence of
probability measures on a Polish space. -/
theorem embed {𝓨 : Type*} [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨]
    [BorelSpace 𝓨] :
    ∃ T : ProbabilityMeasure 𝓨 → (Finset ℕ × ℕ → ℝ),
      (∀ p, ∃ f : 𝓨 →ᵇ NNReal, ∀ ρ : ProbabilityMeasure 𝓨,
        T ρ p = (∫⁻ y, (f y : ℝ≥0∞) ∂(ρ : Measure 𝓨)).toReal) ∧
      Continuous T ∧
      (∀ (ρs : ℕ → ProbabilityMeasure 𝓨) (ρ : ProbabilityMeasure 𝓨),
        (∀ p, Tendsto (fun n => T (ρs n) p) atTop (𝓝 (T ρ p))) → Tendsto ρs atTop (𝓝 ρ)) := by
  classical
  rcases isEmpty_or_nonempty 𝓨 with hE | hNE
  · have hPE : IsEmpty (ProbabilityMeasure 𝓨) := ⟨fun ρ => by
      have h1 : (ρ : Measure 𝓨) Set.univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h1
      exact zero_ne_one h1⟩
    refine ⟨fun _ _ => 0, fun p => ⟨0, fun ρ => (IsEmpty.false ρ).elim⟩, continuous_const,
      fun ρs ρ _ => (IsEmpty.false ρ).elim⟩
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis 𝓨
  have hbne : b.Nonempty := by
    obtain ⟨y⟩ := hNE
    obtain ⟨v, hv, -, -⟩ := hb.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨v, hv⟩
  obtain ⟨U, rfl⟩ := hbc.exists_eq_range hbne
  let C : Finset ℕ → Set 𝓨 := fun t => ⋃ i ∈ t, U i
  have hCo : ∀ t, IsOpen (C t) := fun t =>
    isOpen_biUnion (fun i _ => hb.isOpen ⟨i, rfl⟩)
  have hE : ∀ t, IsClosed (C t)ᶜ := fun t => (hCo t).isClosed_compl
  let T : ProbabilityMeasure 𝓨 → (Finset ℕ × ℕ → ℝ) :=
    fun ρ p => (∫⁻ y, ((hE p.1).apprSeq p.2 y : ℝ≥0∞) ∂(ρ : Measure 𝓨)).toReal
  refine ⟨T, fun p => ⟨(hE p.1).apprSeq p.2, fun ρ => rfl⟩, ?_, ?_⟩
  · refine continuous_pi fun p => ?_
    refine ENNReal.continuousOn_toReal.comp_continuous
      (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction _) (fun ρ => ?_)
    exact (BoundedContinuousFunction.lintegral_lt_top_of_nnreal _ _).ne
  intro ρs ρ h
  have h' : ∀ p : Finset ℕ × ℕ, Tendsto
      (fun n => ∫⁻ y, ((hE p.1).apprSeq p.2 y : ℝ≥0∞) ∂(ρs n : Measure 𝓨)) atTop
      (𝓝 (∫⁻ y, ((hE p.1).apprSeq p.2 y : ℝ≥0∞) ∂(ρ : Measure 𝓨))) := by
    intro p
    exact (ENNReal.tendsto_toReal_iff
      (fun n => (BoundedContinuousFunction.lintegral_lt_top_of_nnreal _ _).ne)
      (BoundedContinuousFunction.lintegral_lt_top_of_nnreal _ _).ne).1 (h p)
  have hEt : ∀ t, limsup (fun n => (ρs n : Measure 𝓨) (C t)ᶜ) atTop ≤ (ρ : Measure 𝓨) (C t)ᶜ := by
    intro t
    refine ge_of_tendsto (HasOuterApproxClosed.tendsto_lintegral_apprSeq (hE t) (ρ : Measure 𝓨))
      (Eventually.of_forall fun j => ?_)
    have hj := h' (t, j)
    rw [← hj.limsup_eq]
    exact limsup_le_limsup (Eventually.of_forall fun n =>
      HasOuterApproxClosed.measure_le_lintegral (hE t) _ j)
  refine tendsto_of_forall_isClosed_limsup_le' (fun F hF => ?_)
  let D : ℕ → Finset ℕ := fun m => (Finset.range m).filter (fun i => U i ⊆ Fᶜ)
  have hanti : Antitone (fun m => (C (D m))ᶜ) := by
    intro m m' h
    apply Set.compl_subset_compl.2
    intro y hy
    simp only [C, D, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range] at hy ⊢
    obtain ⟨i, ⟨him, hiG⟩, hyi⟩ := hy
    exact ⟨i, ⟨lt_of_lt_of_le him h, hiG⟩, hyi⟩
  have hinter : ⋂ m, (C (D m))ᶜ = F := by
    rw [← Set.compl_iUnion]
    have : ⋃ m, C (D m) = Fᶜ := by
      apply Set.Subset.antisymm
      · refine Set.iUnion_subset fun m y hy => ?_
        simp only [C, D, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range] at hy
        obtain ⟨i, ⟨-, hiG⟩, hyi⟩ := hy
        exact hiG hyi
      · intro y hy
        obtain ⟨v, ⟨i, rfl⟩, hyv, hvG⟩ := hb.exists_subset_of_mem_open hy hF.isOpen_compl
        simp only [C, D, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range]
        exact ⟨i + 1, i, ⟨Nat.lt_succ_self i, hvG⟩, hyv⟩
    rw [this, compl_compl]
  have h1 := tendsto_measure_iInter_atTop (μ := (ρ : Measure 𝓨))
    (fun m => (hE (D m)).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at h1
  refine ge_of_tendsto h1 (Eventually.of_forall fun m => ?_)
  refine le_trans ?_ (hEt (D m))
  refine limsup_le_limsup (Eventually.of_forall fun n => measure_mono ?_)
  rw [← hinter]
  exact Set.iInter_subset _ m

/-- The sublevel sets of `K(ν, ·)` are weakly closed. -/
theorem isClosed_sublevel {𝓨 : Type*} [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨]
    [BorelSpace 𝓨] (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (ν : Measure 𝓨) [IsProbabilityMeasure ν] (a : ℝ≥0∞) :
    IsClosed {ρ : ProbabilityMeasure 𝓨 | RWPI.SqrtLasso.transportCost k ν (ρ : Measure 𝓨) ≤ a} := by
  refine IsSeqClosed.isClosed fun ρs ρ hρs hlim => ?_
  have hconv := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim
  have := OTSensitivity.Info.transportCost_lsc k hk ν (fun n => (ρs n : Measure 𝓨))
    (fun n => inferInstance) (ρ : Measure 𝓨) hconv
  refine this.trans ?_
  exact liminf_le_of_frequently_le' (Frequently.of_forall fun n => hρs n)

/-- Measurability of `x ↦ K(ν, κ x)` for a Markov kernel `κ` into a Polish space. -/
theorem measurable_transportCost {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (ν : Measure 𝓨) [IsProbabilityMeasure ν] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    Measurable (fun x => RWPI.SqrtLasso.transportCost k ν (κ x)) := by
  classical
  obtain ⟨T, hTf, hTc, hseq⟩ := embed (𝓨 := 𝓨)
  have hInd : Topology.IsInducing T := by
    rw [Topology.isInducing_iff_nhds]
    intro ρ
    apply le_antisymm
    · exact (hTc.tendsto ρ).le_comap
    · have : Tendsto id (Filter.comap T (𝓝 (T ρ))) (𝓝 ρ) := by
        refine tendsto_of_seq_tendsto fun x hx => ?_
        exact hseq x ρ (tendsto_pi_nhds.1 (tendsto_comap_iff.1 hx))
      exact this
  refine measurable_of_Ioi fun a => ?_
  have hO : IsOpen {ρ : ProbabilityMeasure 𝓨 | a < RWPI.SqrtLasso.transportCost k ν (ρ : Measure 𝓨)} := by
    have := (isClosed_sublevel k hk ν a).isOpen_compl
    simpa only [Set.compl_setOf, not_le] using this
  obtain ⟨V, hV, hpre⟩ := hInd.isOpen_iff.1 hO
  let κP : 𝓧 → ProbabilityMeasure 𝓨 := fun x => ⟨κ x, inferInstance⟩
  have hTκ : Measurable (fun x => T (κP x)) := by
    refine measurable_pi_lambda _ fun p => ?_
    obtain ⟨f, hf⟩ := hTf p
    simp only [hf]
    exact (f.continuous.measurable.coe_nnreal_ennreal.lintegral_kernel).ennreal_toReal
  have : (fun x => RWPI.SqrtLasso.transportCost k ν (κ x)) ⁻¹' Set.Ioi a =
      (fun x => T (κP x)) ⁻¹' V := by
    ext x
    have := congrArg (fun s => κP x ∈ s) hpre
    simp only [Set.mem_preimage, Set.mem_setOf_eq, eq_iff_iff] at this
    simp only [Set.mem_preimage, Set.mem_Ioi]
    exact this.symm
  rw [this]
  exact hTκ hV.measurableSet

end OTInfra

namespace OTRel

/-- Disintegration of `μ` along `G`: `∫_A ∫ g d(μ^G_x) dμ(x) = ∫_A g dμ` for `A ∈ G`. -/
theorem condExpKernel_setLIntegral {𝓧 : Type*} (G : MeasurableSpace 𝓧) [m𝓧 : MeasurableSpace 𝓧]
    [StandardBorelSpace 𝓧] (μ : Measure 𝓧) [IsFiniteMeasure μ] (hG : G ≤ m𝓧)
    (A : Set 𝓧) (hA : MeasurableSet[G] A) (g : 𝓧 → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in A, ∫⁻ z, g z ∂(condExpKernel μ G x) ∂μ = ∫⁻ x in A, g x ∂μ := by
  have hcp := compProd_trim_condExpKernel (μ := μ) hG
  let h : 𝓧 × 𝓧 → ℝ≥0∞ := fun p => A.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * g p.2
  have hh : @Measurable (𝓧 × 𝓧) ℝ≥0∞ (G.prod m𝓧) _ h := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_const.indicator hA).comp (@measurable_fst 𝓧 𝓧 G m𝓧)
    · exact hg.comp (@measurable_snd 𝓧 𝓧 G m𝓧)
  have hind : ∀ (I : 𝓧 → ℝ≥0∞) (x : 𝓧),
      A.indicator (fun _ => (1 : ℝ≥0∞)) x * I x = A.indicator I x := by
    intro I x
    by_cases hx : x ∈ A <;> simp [hx]
  have hAm : MeasurableSet A := hG A hA
  have h1 : ∫⁻ p, h p ∂((μ.trim hG) ⊗ₘ condExpKernel μ G) =
      ∫⁻ x in A, ∫⁻ z, g z ∂(condExpKernel μ G x) ∂μ := by
    rw [Measure.lintegral_compProd hh]
    simp only [h]
    have : ∀ x, ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) x * g z ∂(condExpKernel μ G x) =
        A.indicator (fun _ => (1 : ℝ≥0∞)) x * ∫⁻ z, g z ∂(condExpKernel μ G x) :=
      fun x => lintegral_const_mul _ hg
    simp_rw [this]
    rw [lintegral_trim hG (f := fun a => A.indicator (fun _ => (1 : ℝ≥0∞)) a *
      ∫⁻ z, g z ∂(condExpKernel μ G a))
      ((measurable_const.indicator hA).mul (hg.lintegral_kernel (κ := condExpKernel μ G)))]
    rw [← lintegral_indicator hAm]
    congr 1
    funext x
    exact hind (fun x => ∫⁻ z, g z ∂(condExpKernel μ G x)) x
  have hdiag : @Measurable 𝓧 (𝓧 × 𝓧) m𝓧 (G.prod m𝓧) Function.diag :=
    (Measurable.prodMk (f := id) (g := id) (measurable_id'' hG : @Measurable 𝓧 𝓧 m𝓧 G id)
      measurable_id : @Measurable 𝓧 (𝓧 × 𝓧) m𝓧 (G.prod m𝓧) _)
  have h2 : ∫⁻ p, h p ∂(@Measure.map 𝓧 (𝓧 × 𝓧) m𝓧 (G.prod m𝓧) Function.diag μ) =
      ∫⁻ x in A, g x ∂μ := by
    rw [@lintegral_map 𝓧 (𝓧 × 𝓧) m𝓧 (G.prod m𝓧) μ h Function.diag hh hdiag]
    show ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x * g x ∂μ = ∫⁻ x in A, g x ∂μ
    rw [← lintegral_indicator hAm]
    congr 1
    funext x
    exact hind g x
  rw [← h1, hcp, h2]

end OTRel

open OTSensitivity.Info in
theorem solution {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] (G F : MeasurableSpace 𝓧)
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (hGF : G ≤ F) (hF : F ≤ m𝓧)
    (κG : Kernel 𝓧 𝓨) (hκG : IsCondDistrib P X Y G κG)
    (κF : Kernel 𝓧 𝓨) (hκF : IsCondDistrib P X Y F κF) :
    OTSensitivity.MaxFun.xi k P X Y κG ≤ OTSensitivity.MaxFun.xi k P X Y κF := by
  set μ : Measure 𝓧 := P.map X with hμdef
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsMarkovKernel κG := hκG.1
  haveI : IsMarkovKernel κF := hκF.1
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hGle : G ≤ m𝓧 := hGF.trans hF
  let η : @Kernel 𝓧 𝓧 G m𝓧 := condExpKernel μ G
  -- `κG` as a `G`-kernel
  let κG' : @Kernel 𝓧 𝓨 G _ :=
    @Kernel.mk 𝓧 𝓨 G _ (fun x => κG x)
      (Measure.measurable_of_measurable_coe (mβ := G) (fun x => κG x)
        (fun B hB => hκG.2.1 B hB))
  haveI : IsMarkovKernel κG' := ⟨fun x => by
    exact (inferInstance : IsProbabilityMeasure (κG x))⟩
  let lam : @Kernel 𝓧 𝓨 G _ := κF ∘ₖ η
  have hrect : ∀ A : Set 𝓧, MeasurableSet[G] A → ∀ B : Set 𝓨, MeasurableSet B →
      ((μ.trim hGle) ⊗ₘ κG') (A ×ˢ B) = ((μ.trim hGle) ⊗ₘ lam) (A ×ˢ B) := by
    intro A hA B hB
    rw [Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod hA hB,
      setLIntegral_trim hGle (κG'.measurable_coe hB) hA,
      setLIntegral_trim hGle (lam.measurable_coe hB) hA]
    have hlam : ∀ x, lam x B = ∫⁻ z, κF z B ∂(η x) := fun x => Kernel.comp_apply' _ _ _ hB
    simp_rw [hlam]
    rw [OTRel.condExpKernel_setLIntegral G μ hGle A hA _ (κF.measurable_coe hB)]
    show ∫⁻ x in A, κG x B ∂μ = ∫⁻ x in A, κF x B ∂μ
    rw [← hκG.2.2 A hA B hB, ← hκF.2.2 A (hGF A hA) B hB]
  have hcp : (μ.trim hGle) ⊗ₘ κG' = (μ.trim hGle) ⊗ₘ lam := by
    refine MeasureTheory.ext_of_generate_finite _ (@generateFrom_prod 𝓧 𝓨 G _).symm
      (@isPiSystem_prod 𝓧 𝓨 G _) ?_ ?_
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      exact hrect A hA B hB
    · rw [← Set.univ_prod_univ]
      exact hrect _ (@MeasurableSet.univ 𝓧 G) _ MeasurableSet.univ
  have hae := Kernel.ae_eq_of_compProd_eq hcp
  have hmix : ∀ᵐ x ∂μ, κG x = (η x).bind κF := by
    have := ae_of_ae_trim hGle hae
    filter_upwards [this] with x hx
    have h2 : lam x = (η x).bind κF := Kernel.comp_apply _ _ _
    rw [← h2]
    exact hx
  have hmeas := OTInfra.measurable_transportCost k hk (P.map Y) κF
  have htower : ∫⁻ x', ∫⁻ x, RWPI.SqrtLasso.transportCost k (P.map Y) (κF x) ∂(η x') ∂μ =
      ∫⁻ x, RWPI.SqrtLasso.transportCost k (P.map Y) (κF x) ∂μ := by
    have := OTRel.condExpKernel_setLIntegral G μ hGle Set.univ (@MeasurableSet.univ 𝓧 G) _ hmeas
    simpa using this
  unfold OTSensitivity.MaxFun.xi
  calc ∫⁻ x, RWPI.SqrtLasso.transportCost k (P.map Y) (κG x) ∂(P.map X)
      = ∫⁻ x, RWPI.SqrtLasso.transportCost k (P.map Y) ((η x).bind κF) ∂μ :=
        lintegral_congr_ae (hmix.mono fun x hx => by dsimp only; rw [hx])
    _ ≤ ∫⁻ x', ∫⁻ x, RWPI.SqrtLasso.transportCost k (P.map Y) (κF x) ∂(η x') ∂μ :=
        lintegral_mono fun x' => mixture_convexity k hk (P.map Y) (η x') κF
    _ = ∫⁻ x, RWPI.SqrtLasso.transportCost k (P.map Y) (κF x) ∂(P.map X) := htower
