-- Prove2me | solution 1 for OTSensitivity.Info.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:36:49.029328+00:00
-- url     : https://prove2.me/submissions/bf150d6d-ecee-4d5e-a97f-c4e85281d162

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting
import Theorems.Thm_OTSensitivity_Info_transportCost_lsc
import Theorems.Thm_OTSensitivity_Info_ae_weak_convergence
import Theorems.Thm_OTSensitivity_Info_relative_monotonicity

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace OTIMeas

/-- Measurability of `x ↦ K(ν, κ x)` for a Markov kernel `κ` into a Polish space. -/
theorem measurable_transportCost {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (ν : Measure 𝓨) [IsProbabilityMeasure ν] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    Measurable (fun x => RWPI.SqrtLasso.transportCost k ν (κ x)) := by
  classical
  rcases isEmpty_or_nonempty 𝓨 with hE | hNE
  · have : IsEmpty 𝓧 := ⟨fun x => by
      have h1 : κ x Set.univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h1
      exact zero_ne_one h1⟩
    exact Subsingleton.measurable
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
  let T : ProbabilityMeasure 𝓨 → (Finset ℕ × ℕ → ℝ≥0∞) :=
    fun ρ p => ∫⁻ y, ((hE p.1).apprSeq p.2 y : ℝ≥0∞) ∂(ρ : Measure 𝓨)
  -- sequential criterion
  have hseq : ∀ (ρs : ℕ → ProbabilityMeasure 𝓨) (ρ : ProbabilityMeasure 𝓨),
      Tendsto (fun n => T (ρs n)) atTop (𝓝 (T ρ)) → Tendsto ρs atTop (𝓝 ρ) := by
    intro ρs ρ h
    rw [tendsto_pi_nhds] at h
    -- limsup bound for the closed sets `E t`
    have hEt : ∀ t, limsup (fun n => (ρs n : Measure 𝓨) (C t)ᶜ) atTop ≤ (ρ : Measure 𝓨) (C t)ᶜ := by
      intro t
      refine ge_of_tendsto (HasOuterApproxClosed.tendsto_lintegral_apprSeq (hE t) (ρ : Measure 𝓨))
        (Eventually.of_forall fun j => ?_)
      have hj : Tendsto (fun n => ∫⁻ y, ((hE t).apprSeq j y : ℝ≥0∞) ∂(ρs n : Measure 𝓨)) atTop
          (𝓝 (∫⁻ y, ((hE t).apprSeq j y : ℝ≥0∞) ∂(ρ : Measure 𝓨))) := h (t, j)
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
  have hTc : Continuous T := continuous_pi fun p =>
    ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction _
  have hInd : Topology.IsInducing T := by
    rw [Topology.isInducing_iff_nhds]
    intro ρ
    apply le_antisymm
    · exact (hTc.tendsto ρ).le_comap
    · have : Tendsto id (Filter.comap T (𝓝 (T ρ))) (𝓝 ρ) := by
        refine tendsto_of_seq_tendsto fun x hx => ?_
        exact hseq x ρ (tendsto_comap_iff.1 hx)
      exact this
  -- lower semicontinuity
  have hclosed : ∀ a : ℝ≥0∞, IsClosed {ρ : ProbabilityMeasure 𝓨 |
      RWPI.SqrtLasso.transportCost k ν (ρ : Measure 𝓨) ≤ a} := by
    intro a
    refine IsSeqClosed.isClosed fun ρs ρ hρs hlim => ?_
    have hconv := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim
    have := OTSensitivity.Info.transportCost_lsc k hk ν (fun n => (ρs n : Measure 𝓨))
      (fun n => inferInstance) (ρ : Measure 𝓨) hconv
    refine this.trans ?_
    refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => hρs n)
  refine measurable_of_Ioi fun a => ?_
  have hO : IsOpen {ρ : ProbabilityMeasure 𝓨 | a < RWPI.SqrtLasso.transportCost k ν (ρ : Measure 𝓨)} := by
    have := (hclosed a).isOpen_compl
    simpa only [Set.compl_setOf, not_le] using this
  obtain ⟨V, hV, hpre⟩ := hInd.isOpen_iff.1 hO
  let κP : 𝓧 → ProbabilityMeasure 𝓨 := fun x => ⟨κ x, inferInstance⟩
  have hTκ : Measurable (fun x => T (κP x)) := by
    refine measurable_pi_lambda _ fun p => ?_
    exact ((hE p.1).apprSeq p.2).continuous.measurable.coe_nnreal_ennreal.lintegral_kernel
  have : (fun x => RWPI.SqrtLasso.transportCost k ν (κ x)) ⁻¹' Set.Ioi a =
      (fun x => T (κP x)) ⁻¹' V := by
    ext x
    have := congrArg (fun s => κP x ∈ s) hpre
    simp only [Set.mem_preimage, Set.mem_setOf_eq, eq_iff_iff] at this
    simp only [Set.mem_preimage, Set.mem_Ioi]
    exact this.symm
  rw [this]
  exact hTκ hV.measurableSet

end OTIMeas

open OTSensitivity.Info in
theorem solution {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] (Fs : ℕ → MeasurableSpace 𝓧)
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (hmono : Monotone Fs) (hle : ∀ n, Fs n ≤ m𝓧)
    (κs : ℕ → Kernel 𝓧 𝓨) (hκs : ∀ n, IsCondDistrib P X Y (Fs n) (κs n))
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y (⨆ n, Fs n) κ) :
    Tendsto (fun n => OTSensitivity.MaxFun.xi k P X Y (κs n)) atTop (𝓝 (OTSensitivity.MaxFun.xi k P X Y κ)) := by
  have hM : ∀ n, IsMarkovKernel (κs n) := fun n => (hκs n).1
  haveI : IsMarkovKernel κ := hκ.1
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  -- upper bound: monotonicity in the information (Theorem 8 relative to `⨆ n, Fs n`)
  have hup : ∀ n, OTSensitivity.MaxFun.xi k P X Y (κs n) ≤ OTSensitivity.MaxFun.xi k P X Y κ :=
    fun n => relative_monotonicity (Fs n) (⨆ n, Fs n) k hk P X Y hX hY (le_iSup Fs n)
      (iSup_le hle) (κs n) (hκs n) κ hκ
  -- lower bound: a.e. weak convergence, lower semicontinuity of `K(ν, ·)`, and Fatou
  have hweak := ae_weak_convergence Fs P X Y hX hY hmono hle κs hκs κ hκ
  have hpt : ∀ᵐ x ∂(P.map X), RWPI.SqrtLasso.transportCost k (P.map Y) (κ x) ≤
      liminf (fun n => RWPI.SqrtLasso.transportCost k (P.map Y) (κs n x)) atTop := by
    filter_upwards [hweak] with x hx
    exact transportCost_lsc k hk (P.map Y) (fun n => κs n x)
      (fun n => by haveI := hM n; infer_instance) (κ x) hx
  have hlow : OTSensitivity.MaxFun.xi k P X Y κ ≤
      liminf (fun n => OTSensitivity.MaxFun.xi k P X Y (κs n)) atTop := by
    unfold OTSensitivity.MaxFun.xi
    calc ∫⁻ x, RWPI.SqrtLasso.transportCost k (P.map Y) (κ x) ∂(P.map X)
        ≤ ∫⁻ x, liminf (fun n => RWPI.SqrtLasso.transportCost k (P.map Y) (κs n x)) atTop
            ∂(P.map X) := lintegral_mono_ae hpt
      _ ≤ liminf (fun n => ∫⁻ x, RWPI.SqrtLasso.transportCost k (P.map Y) (κs n x) ∂(P.map X))
            atTop :=
          lintegral_liminf_le (fun n => by
            haveI := hM n
            exact OTIMeas.measurable_transportCost k hk (P.map Y) (κs n))
  have hupl : limsup (fun n => OTSensitivity.MaxFun.xi k P X Y (κs n)) atTop ≤
      OTSensitivity.MaxFun.xi k P X Y κ :=
    limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hup)
  exact tendsto_of_le_liminf_of_limsup_le hlow hupl
