-- Prove2me | solution 1 for OTSensitivity.Info.theorem_8_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:00:14.100987+00:00
-- url     : https://prove2.me/submissions/5df9f1d2-0682-4eed-aa4c-a08811e3c25f

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting
import Definitions.Def_OTSensitivity_Info_InjectiveAE
import Theorems.Thm_OTSensitivity_Info_transportCost_lsc
import Theorems.Thm_OTSensitivity_Info_relative_monotonicity

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

namespace OTGen

/-- Uniqueness of disintegrations: kernels with the same set integrals agree a.e. -/
theorem uniq {β 𝓨 : Type*} [mβ : MeasurableSpace β] [m𝓨 : MeasurableSpace 𝓨]
    [MeasurableSpace.CountablyGenerated 𝓨]
    (σ : Measure β) [IsFiniteMeasure σ] (κ1 κ2 : Kernel β 𝓨) [IsMarkovKernel κ1]
    [IsMarkovKernel κ2]
    (h : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ∫⁻ u in A, κ1 u B ∂σ = ∫⁻ u in A, κ2 u B ∂σ) :
    ∀ᵐ u ∂σ, κ1 u = κ2 u := by
  have hcp : σ ⊗ₘ κ1 = σ ⊗ₘ κ2 := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      rw [Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod hA hB, h A hA B hB]
    · rw [← Set.univ_prod_univ, Measure.compProd_apply_prod MeasurableSet.univ MeasurableSet.univ,
        Measure.compProd_apply_prod MeasurableSet.univ MeasurableSet.univ,
        h _ MeasurableSet.univ _ MeasurableSet.univ]
  exact Kernel.ae_eq_of_compProd_eq hcp

end OTGen

open OTSensitivity.Info in
theorem solution {Ω 𝓧 𝓨 𝓤 : Type*} [MeasurableSpace Ω]
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    [TopologicalSpace 𝓤] [PolishSpace 𝓤] [m𝓤 : MeasurableSpace 𝓤] [BorelSpace 𝓤]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (g : 𝓧 → 𝓤) (hg : Measurable g)
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y m𝓧 κ)
    (κU : Kernel 𝓤 𝓨) (hκU : IsCondDistrib P (g ∘ X) Y m𝓤 κU)
    (κg : Kernel 𝓧 𝓨) (hκg : IsCondDistrib P X Y (MeasurableSpace.comap g m𝓤) κg) :
    OTSensitivity.MaxFun.xi k P (g ∘ X) Y κU ≤ OTSensitivity.MaxFun.xi k P X Y κ ∧
      OTSensitivity.MaxFun.xi k P (g ∘ X) Y κU = OTSensitivity.MaxFun.xi k P X Y κg ∧
      (IsInjectiveAE (P.map X) g → OTSensitivity.MaxFun.xi k P X Y κ = OTSensitivity.MaxFun.xi k P (g ∘ X) Y κU) := by
  set μ : Measure 𝓧 := P.map X with hμdef
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsMarkovKernel κ := hκ.1
  haveI : IsMarkovKernel κU := hκU.1
  haveI : IsMarkovKernel κg := hκg.1
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hmap : μ.map g = P.map (g ∘ X) := Measure.map_map hg hX
  have hG : (MeasurableSpace.comap g m𝓤) ≤ m𝓧 := hg.comap_le
  have hgG : @Measurable 𝓧 𝓤 (MeasurableSpace.comap g m𝓤) m𝓤 g := comap_measurable g
  have hid : @Measurable 𝓧 𝓧 m𝓧 (MeasurableSpace.comap g m𝓤) id := measurable_id'' hG
  -- Step 1: `κg x = κU (g x)` for `μ`-a.e. `x`
  let κg' : @Kernel 𝓧 𝓨 (MeasurableSpace.comap g m𝓤) _ :=
    @Kernel.mk 𝓧 𝓨 (MeasurableSpace.comap g m𝓤) _ (fun x => κg x)
      (Measure.measurable_of_measurable_coe (mβ := (MeasurableSpace.comap g m𝓤)) (fun x => κg x)
        (fun B hB => hκg.2.1 B hB))
  haveI : @IsMarkovKernel 𝓧 𝓨 (MeasurableSpace.comap g m𝓤) _ κg' :=
    ⟨fun x => (inferInstance : IsProbabilityMeasure (κg x))⟩
  let κUg : @Kernel 𝓧 𝓨 (MeasurableSpace.comap g m𝓤) _ := Kernel.comap (mγ := (MeasurableSpace.comap g m𝓤)) κU g hgG
  haveI : @IsMarkovKernel 𝓧 𝓨 (MeasurableSpace.comap g m𝓤) _ κUg :=
    ⟨fun x => (inferInstance : IsProbabilityMeasure (κU (g x)))⟩
  let σG : @Measure 𝓧 (MeasurableSpace.comap g m𝓤) := @Measure.map 𝓧 𝓧 m𝓧 (MeasurableSpace.comap g m𝓤) id μ
  haveI : @IsFiniteMeasure 𝓧 (MeasurableSpace.comap g m𝓤) σG := ⟨by
    rw [Measure.map_apply_of_aemeasurable (mβ := (MeasurableSpace.comap g m𝓤)) ⟨id, hid, Filter.EventuallyEq.rfl⟩
      (@MeasurableSet.univ 𝓧 (MeasurableSpace.comap g m𝓤))]
    exact measure_lt_top _ _⟩
  have hconv : ∀ (f : 𝓧 → ℝ≥0∞), Measurable[(MeasurableSpace.comap g m𝓤)] f → ∀ A, MeasurableSet[(MeasurableSpace.comap g m𝓤)] A →
      ∫⁻ u in A, f u ∂σG = ∫⁻ x in A, f x ∂μ := by
    intro f hf A hA
    rw [@setLIntegral_map 𝓧 𝓧 m𝓧 (MeasurableSpace.comap g m𝓤) μ f id A hA hf hid]
    rfl
  have hrect : ∀ A, MeasurableSet[(MeasurableSpace.comap g m𝓤)] A → ∀ B, MeasurableSet B →
      ∫⁻ u in A, κg' u B ∂σG = ∫⁻ u in A, κUg u B ∂σG := by
    intro A hA B hB
    refine (hconv (fun u => κg u B) (hκg.2.1 B hB) A hA).trans ?_
    refine Eq.trans ?_ (hconv (fun u => κU (g u) B) ((κU.measurable_coe hB).comp hgG) A hA).symm
    obtain ⟨A', hA', rfl⟩ := hA
    show ∫⁻ x in g ⁻¹' A', κg x B ∂μ = ∫⁻ x in g ⁻¹' A', κU (g x) B ∂μ
    rw [← hκg.2.2 _ ⟨A', hA', rfl⟩ B hB, ← setLIntegral_map hA' (κU.measurable_coe hB) hg, hmap,
      ← hκU.2.2 A' hA' B hB]
    rfl
  have hae1 := OTGen.uniq (mβ := (MeasurableSpace.comap g m𝓤)) σG κg' κUg hrect
  have hae2 : ∀ᵐ x ∂μ, κg x = κU (g x) := by
    refine ae_of_ae_map (mβ := (MeasurableSpace.comap g m𝓤)) (f := id) (μ := μ) ?_ hae1
    exact ⟨id, hid, Filter.EventuallyEq.rfl⟩
  -- Step 2: `ξ(Y, U) = ξ(Y, X | σ(g))`
  have hKU := OTInfra.measurable_transportCost k hk (P.map Y) κU
  have h2 : OTSensitivity.MaxFun.xi k P (g ∘ X) Y κU = OTSensitivity.MaxFun.xi k P X Y κg := by
    unfold OTSensitivity.MaxFun.xi
    rw [← hmap, lintegral_map hKU hg]
    refine lintegral_congr_ae (hae2.mono fun x hx => ?_)
    dsimp only
    rw [hx]
  -- Step 3: monotonicity
  have h1 : OTSensitivity.MaxFun.xi k P (g ∘ X) Y κU ≤ OTSensitivity.MaxFun.xi k P X Y κ := by
    rw [h2]
    exact relative_monotonicity (MeasurableSpace.comap g m𝓤) m𝓧 k hk P X Y hX hY hG le_rfl κg hκg κ hκ
  refine ⟨h1, h2, fun hinj => ?_⟩
  -- Step 4: injective case
  obtain ⟨S, hS, hSc, hinjS⟩ := hinj
  have haeS : ∀ᵐ x ∂μ, x ∈ S := by
    rw [ae_iff]
    simpa [Set.compl_def] using hSc
  have hrect2 : ∀ A, MeasurableSet A → ∀ B, MeasurableSet B →
      ∫⁻ x in A, κg x B ∂μ = ∫⁻ x in A, κ x B ∂μ := by
    intro A hA B hB
    have hA' : MeasurableSet (g '' (A ∩ S)) :=
      (hA.inter hS).image_of_measurable_injOn hg (hinjS.mono Set.inter_subset_right)
    have hAA : A =ᵐ[μ] (g ⁻¹' (g '' (A ∩ S)) : Set 𝓧) := by
      filter_upwards [haeS] with x hx
      apply propext
      constructor
      · intro hxA
        exact ⟨x, ⟨hxA, hx⟩, rfl⟩
      · rintro ⟨a, ⟨haA, haS⟩, hga⟩
        rw [← hinjS haS hx hga]
        exact haA
    rw [setLIntegral_congr hAA, setLIntegral_congr hAA,
      ← hκg.2.2 _ ⟨_, hA', rfl⟩ B hB, ← hκ.2.2 _ (hg hA') B hB]
  have hae3 := OTGen.uniq μ κg κ hrect2
  have h3 : OTSensitivity.MaxFun.xi k P X Y κg = OTSensitivity.MaxFun.xi k P X Y κ := by
    unfold OTSensitivity.MaxFun.xi
    refine lintegral_congr_ae (hae3.mono fun x hx => ?_)
    dsimp only
    rw [hx]
  rw [h2, h3]
