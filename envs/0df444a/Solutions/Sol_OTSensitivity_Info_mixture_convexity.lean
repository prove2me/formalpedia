-- Prove2me | solution 1 for OTSensitivity.Info.mixture_convexity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:44:53.69805+00:00
-- url     : https://prove2.me/submissions/8ee3505c-431f-47f1-9b2f-eee570135474

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting
import Theorems.Thm_OTSensitivity_Info_transportCost_lsc

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

/-- Existence of `ε`-optimal couplings. -/
theorem exists_coupling_le {𝓨 : Type*} [MeasurableSpace 𝓨] (k : 𝓨 → 𝓨 → ℝ≥0∞)
    (ν σ : Measure 𝓨) [IsProbabilityMeasure ν] [IsProbabilityMeasure σ] (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ π : Measure (𝓨 × 𝓨), (IsProbabilityMeasure π ∧ π.map Prod.fst = ν ∧ π.map Prod.snd = σ) ∧
      ∫⁻ w, k w.1 w.2 ∂π ≤ RWPI.SqrtLasso.transportCost k ν σ + ε := by
  by_cases htop : RWPI.SqrtLasso.transportCost k ν σ = ⊤
  · refine ⟨ν.prod σ, ⟨inferInstance, ?_, ?_⟩, by rw [htop]; simp⟩
    · simp [Measure.map_fst_prod]
    · simp [Measure.map_snd_prod]
  · have hlt : RWPI.SqrtLasso.transportCost k ν σ < RWPI.SqrtLasso.transportCost k ν σ + ε :=
      ENNReal.lt_add_right htop hε.ne'
    have h2 := hlt
    unfold RWPI.SqrtLasso.transportCost at h2
    conv_lhs at h2 => skip
    rw [iInf_lt_iff] at h2
    obtain ⟨π, hπ⟩ := h2
    rw [iInf_lt_iff] at hπ
    obtain ⟨h, hh⟩ := hπ
    exact ⟨π, h, hh.le⟩

/-- Countable convexity of `K(ν, ·)`. -/
theorem countable_convexity {𝓨 : Type*} [MeasurableSpace 𝓨] (k : 𝓨 → 𝓨 → ℝ≥0∞)
    (hkm : Measurable (Function.uncurry k))
    (ν : Measure 𝓨) [IsProbabilityMeasure ν] (σ : ℕ → Measure 𝓨) (hσ : ∀ i, IsProbabilityMeasure (σ i))
    (w : ℕ → ℝ≥0∞) (hw : ∑' i, w i = 1) :
    RWPI.SqrtLasso.transportCost k ν (Measure.sum fun i => w i • σ i) ≤
      ∑' i, w i * RWPI.SqrtLasso.transportCost k ν (σ i) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hex := fun i => @exists_coupling_le 𝓨 _ k ν (σ i) _ (hσ i) ε (by exact_mod_cast hε)
  choose π hπ hcost using hex
  let πs : Measure (𝓨 × 𝓨) := Measure.sum fun i => w i • π i
  have hprob : IsProbabilityMeasure πs := by
    constructor
    simp only [πs, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, smul_eq_mul]
    have : ∀ i, (π i) Set.univ = 1 := fun i => by haveI := (hπ i).1; exact measure_univ
    simp [this, hw]
  have hfst : πs.map Prod.fst = ν := by
    ext s hs
    rw [Measure.map_apply measurable_fst hs]
    simp only [πs, Measure.sum_apply _ (measurable_fst hs), Measure.smul_apply, smul_eq_mul]
    have : ∀ i, (π i) (Prod.fst ⁻¹' s) = ν s := fun i => by
      rw [← Measure.map_apply measurable_fst hs, (hπ i).2.1]
    simp only [this]
    rw [ENNReal.tsum_mul_right, hw, one_mul]
  have hsnd : πs.map Prod.snd = Measure.sum fun i => w i • σ i := by
    ext s hs
    rw [Measure.map_apply measurable_snd hs]
    simp only [πs, Measure.sum_apply _ (measurable_snd hs), Measure.sum_apply _ hs,
      Measure.smul_apply, smul_eq_mul]
    congr 1
    funext i
    rw [← Measure.map_apply measurable_snd hs, (hπ i).2.2]
  have hcostπ : ∫⁻ z, k z.1 z.2 ∂πs = ∑' i, w i * ∫⁻ z, k z.1 z.2 ∂(π i) := by
    simp only [πs, lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]
  calc RWPI.SqrtLasso.transportCost k ν (Measure.sum fun i => w i • σ i)
      ≤ ∫⁻ z, k z.1 z.2 ∂πs := by
        unfold RWPI.SqrtLasso.transportCost
        exact iInf₂_le πs ⟨hprob, hfst, hsnd⟩
    _ = ∑' i, w i * ∫⁻ z, k z.1 z.2 ∂(π i) := hcostπ
    _ ≤ ∑' i, w i * (RWPI.SqrtLasso.transportCost k ν (σ i) + ε) :=
        ENNReal.tsum_le_tsum fun i => by gcongr; exact hcost i
    _ = ∑' i, w i * RWPI.SqrtLasso.transportCost k ν (σ i) + ε := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hw, one_mul]

end OTInfra

namespace OTInfra

theorem mixture {𝓧 𝓨 : Type*} [m𝓧 : MeasurableSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (ν : Measure 𝓨) [IsProbabilityMeasure ν]
    (ρ : Measure 𝓧) [IsProbabilityMeasure ρ] (η : Kernel 𝓧 𝓨) [IsMarkovKernel η] :
    RWPI.SqrtLasso.transportCost k ν (ρ.bind η)
      ≤ ∫⁻ x, RWPI.SqrtLasso.transportCost k ν (η x) ∂ρ := by
  classical
  set F : Measure 𝓨 → ℝ≥0∞ := fun σ => RWPI.SqrtLasso.transportCost k ν σ with hFdef
  have hFη : Measurable (fun x => F (η x)) := measurable_transportCost k hk ν η
  have hkm : Measurable (Function.uncurry k) := hk.1.measurable
  obtain ⟨T, hTf, hTc, hseq⟩ := embed (𝓨 := 𝓨)
  let Φ : ProbabilityMeasure 𝓨 → (Finset ℕ × ℕ → ℝ) × ℝ≥0∞ :=
    fun σ => (T σ, F (σ : Measure 𝓨))
  let S : Set ((Finset ℕ × ℕ → ℝ) × ℝ≥0∞) := Set.range Φ
  let νP : ProbabilityMeasure 𝓨 := ⟨ν, inferInstance⟩
  haveI : Nonempty S := ⟨⟨Φ νP, νP, rfl⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq S
  have hσex : ∀ i, ∃ σ : ProbabilityMeasure 𝓨, Φ σ = (u i : (Finset ℕ × ℕ → ℝ) × ℝ≥0∞) :=
    fun i => (u i).2
  choose σs hσs using hσex
  obtain ⟨e, he⟩ := exists_surjective_nat (Finset ℕ × ℕ)
  let ηP : 𝓧 → ProbabilityMeasure 𝓨 := fun x => ⟨η x, inferInstance⟩
  let εm : ℕ → ℝ≥0∞ := fun m => ((m + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hεm : ∀ m, 0 < εm m := fun m => ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
  let Cond : ℕ → 𝓧 → ℕ → Prop := fun m x i =>
    (∀ j < m, |T (σs i) (e j) - T (ηP x) (e j)| < 1 / ((m : ℝ) + 1)) ∧
      F (σs i : Measure 𝓨) ≤ F (η x) + εm m
  have hex : ∀ m x, ∃ i, Cond m x i := by
    intro m x
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    let W1 : Set ((Finset ℕ × ℕ → ℝ) × ℝ≥0∞) :=
      ⋂ j ∈ Finset.range m, {q | |q.1 (e j) - T (ηP x) (e j)| < 1 / ((m : ℝ) + 1)}
    have hW1 : IsOpen W1 := by
      refine isOpen_biInter_finset fun j _ => ?_
      exact isOpen_lt (by fun_prop) continuous_const
    have hmem1 : Φ (ηP x) ∈ W1 := by
      simp only [W1, Set.mem_iInter, Set.mem_setOf_eq]
      intro j _
      show |(Φ (ηP x)).1 (e j) - T (ηP x) (e j)| < 1 / ((m : ℝ) + 1)
      simp only [Φ, sub_self, abs_zero]
      exact hpos
    by_cases hFt : F (η x) = ⊤
    · let s : Set S := Subtype.val ⁻¹' W1
      have hs : IsOpen s := continuous_subtype_val.isOpen_preimage _ hW1
      have hsne : s.Nonempty := ⟨⟨Φ (ηP x), ηP x, rfl⟩, hmem1⟩
      obtain ⟨i, hi⟩ := hu.exists_mem_open hs hsne
      refine ⟨i, ?_, by rw [hFt]; simp⟩
      intro j hj
      have := hi
      simp only [s, W1, Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq] at this
      have h2 := this j (Finset.mem_range.2 hj)
      rw [← hσs i] at h2
      exact h2
    · let W : Set ((Finset ℕ × ℕ → ℝ) × ℝ≥0∞) := W1 ∩ {q | q.2 < F (η x) + εm m}
      have hW : IsOpen W := hW1.inter (isOpen_lt continuous_snd continuous_const)
      have hmem : Φ (ηP x) ∈ W := ⟨hmem1, ENNReal.lt_add_right hFt (hεm m).ne'⟩
      let s : Set S := Subtype.val ⁻¹' W
      have hs : IsOpen s := continuous_subtype_val.isOpen_preimage _ hW
      have hsne : s.Nonempty := ⟨⟨Φ (ηP x), ηP x, rfl⟩, hmem⟩
      obtain ⟨i, hi⟩ := hu.exists_mem_open hs hsne
      have hi' : Φ (σs i) ∈ W := by rw [hσs i]; exact hi
      refine ⟨i, ?_, hi'.2.le⟩
      intro j hj
      have := hi'.1
      simp only [W1, Set.mem_iInter, Set.mem_setOf_eq] at this
      exact this j (Finset.mem_range.2 hj)
  -- measurability of the selection
  have hTη : ∀ p, Measurable (fun x => T (ηP x) p) := by
    intro p
    obtain ⟨f, hf⟩ := hTf p
    simp only [hf]
    exact (f.continuous.measurable.coe_nnreal_ennreal.lintegral_kernel).ennreal_toReal
  have hCond : ∀ m i, MeasurableSet {x | Cond m x i} := by
    intro m i
    have hA : MeasurableSet {x | ∀ j < m, |T (σs i) (e j) - T (ηP x) (e j)| < 1 / ((m : ℝ) + 1)} := by
      have : {x | ∀ j < m, |T (σs i) (e j) - T (ηP x) (e j)| < 1 / ((m : ℝ) + 1)} =
          ⋂ j ∈ Finset.range m, {x | |T (σs i) (e j) - T (ηP x) (e j)| < 1 / ((m : ℝ) + 1)} := by
        ext x; simp
      rw [this]
      refine Finset.measurableSet_biInter _ fun j _ => ?_
      exact measurableSet_lt (continuous_abs.measurable.comp (measurable_const.sub (hTη (e j))))
        measurable_const
    have hB : MeasurableSet {x | F (σs i : Measure 𝓨) ≤ F (η x) + εm m} :=
      measurableSet_le measurable_const (hFη.add_const _)
    exact hA.inter hB
  let idx : ℕ → 𝓧 → ℕ := fun m x => Nat.find (hex m x)
  have hidx : ∀ m, Measurable (idx m) := by
    intro m
    refine measurable_to_countable' fun i => ?_
    have : idx m ⁻¹' {i} = {x | Cond m x i} ∩ ⋂ j ∈ Finset.range i, {x | Cond m x j}ᶜ := by
      ext x
      simp only [idx, Set.mem_preimage, Set.mem_singleton_iff, Nat.find_eq_iff, Set.mem_inter_iff,
        Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
    rw [this]
    exact (hCond m i).inter (Finset.measurableSet_biInter _ fun j _ => (hCond m j).compl)
  have hidxC : ∀ m x, Cond m x (idx m x) := fun m x => Nat.find_spec (hex m x)
  -- the countable mixtures
  let w : ℕ → ℕ → ℝ≥0∞ := fun m i => (ρ.map (idx m)) {i}
  have hsumw : ∀ m (g : ℕ → ℝ≥0∞), ∑' i, w m i * g i = ∫⁻ x, g (idx m x) ∂ρ := by
    intro m g
    rw [← lintegral_map (measurable_from_nat (f := g)) (hidx m), lintegral_countable']
    exact tsum_congr fun i => mul_comm _ _
  have hw1 : ∀ m, ∑' i, w m i = 1 := by
    intro m
    have := hsumw m (fun _ => 1)
    simpa using this
  let mix : ℕ → Measure 𝓨 := fun m => Measure.sum fun i => w m i • (σs i : Measure 𝓨)
  have hmixP : ∀ m, IsProbabilityMeasure (mix m) := by
    intro m
    constructor
    simp only [mix, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    exact hw1 m
  have hmixint : ∀ m (g : 𝓨 → ℝ≥0∞), ∫⁻ y, g y ∂(mix m) =
      ∫⁻ x, ∫⁻ y, g y ∂(σs (idx m x) : Measure 𝓨) ∂ρ := by
    intro m g
    simp only [mix, lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul]
    exact hsumw m (fun i => ∫⁻ y, g y ∂(σs i : Measure 𝓨))
  -- pointwise weak convergence of the selected measures
  have hptw : ∀ x, Tendsto (fun m => σs (idx m x)) atTop (𝓝 (ηP x)) := by
    intro x
    refine hseq _ _ fun p => ?_
    obtain ⟨j, rfl⟩ := he p
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨max N (j + 1), fun m hm => ?_⟩
    have hjm : j < m := lt_of_lt_of_le (Nat.lt_succ_self j) (le_trans (le_max_right _ _) hm)
    have h1 := (hidxC m x).1 j hjm
    rw [Real.dist_eq]
    refine lt_of_lt_of_le h1 (le_trans ?_ hN.le)
    have hNm : (N : ℝ) ≤ m := by exact_mod_cast le_trans (le_max_left _ _) hm
    gcongr
  have hbindP : IsProbabilityMeasure (ρ.bind η) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ η.measurable.aemeasurable]
    simp
  let mixP : ℕ → ProbabilityMeasure 𝓨 := fun m => ⟨mix m, hmixP m⟩
  let bP : ProbabilityMeasure 𝓨 := ⟨ρ.bind η, hbindP⟩
  have hconvP : Tendsto mixP atTop (𝓝 bP) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto]
    intro f
    simp only [mixP, bP, ProbabilityMeasure.coe_mk]
    rw [Measure.lintegral_bind η.measurable.aemeasurable
      f.continuous.measurable.coe_nnreal_ennreal.aemeasurable]
    simp_rw [hmixint]
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ((nndist f 0 : NNReal) : ℝ≥0∞))
      (fun m => ?_) (fun m => Eventually.of_forall fun x => ?_) (by simp) ?_
    · exact (measurable_from_nat (f := fun i => ∫⁻ y, (f y : ℝ≥0∞) ∂(σs i : Measure 𝓨))).comp
        (hidx m)
    · calc ∫⁻ y, (f y : ℝ≥0∞) ∂(σs (idx m x) : Measure 𝓨)
          ≤ ∫⁻ _, ((nndist f 0 : NNReal) : ℝ≥0∞) ∂(σs (idx m x) : Measure 𝓨) := by
            refine lintegral_mono fun y => ?_
            exact ENNReal.coe_le_coe.2 (BoundedContinuousFunction.NNReal.upper_bound f y)
        _ = ((nndist f 0 : NNReal) : ℝ≥0∞) := by simp
    · refine Eventually.of_forall fun x => ?_
      have := (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 (hptw x)) f
      exact this
  have hconv := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconvP
  have hlsc := OTSensitivity.Info.transportCost_lsc k hk ν mix hmixP (ρ.bind η) hconv
  have hbound : ∀ m, F (mix m) ≤ ∫⁻ x, F (η x) ∂ρ + εm m := by
    intro m
    calc F (mix m) ≤ ∑' i, w m i * F (σs i : Measure 𝓨) :=
          countable_convexity k hkm ν (fun i => (σs i : Measure 𝓨)) (fun i => inferInstance)
            (w m) (hw1 m)
      _ = ∫⁻ x, F (σs (idx m x) : Measure 𝓨) ∂ρ := hsumw m _
      _ ≤ ∫⁻ x, (F (η x) + εm m) ∂ρ := lintegral_mono fun x => (hidxC m x).2
      _ = ∫⁻ x, F (η x) ∂ρ + εm m := by
          rw [lintegral_add_right _ measurable_const]; simp
  have hεlim : Tendsto εm atTop (𝓝 0) := by
    have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    simpa [εm, Function.comp_def] using this
  have hlim2 : Tendsto (fun m => ∫⁻ x, F (η x) ∂ρ + εm m) atTop (𝓝 (∫⁻ x, F (η x) ∂ρ)) := by
    have := (tendsto_const_nhds (x := ∫⁻ x, F (η x) ∂ρ)).add hεlim
    simpa using this
  calc RWPI.SqrtLasso.transportCost k ν (ρ.bind η)
      ≤ liminf (fun m => F (mix m)) atTop := hlsc
    _ ≤ liminf (fun m => ∫⁻ x, F (η x) ∂ρ + εm m) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = ∫⁻ x, F (η x) ∂ρ := hlim2.liminf_eq

end OTInfra

theorem solution {𝓧 𝓨 : Type*}
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (ν : Measure 𝓨) [IsProbabilityMeasure ν]
    (ρ : Measure 𝓧) [IsProbabilityMeasure ρ] (η : Kernel 𝓧 𝓨) [IsMarkovKernel η] :
    RWPI.SqrtLasso.transportCost k ν (ρ.bind η)
      ≤ ∫⁻ x, RWPI.SqrtLasso.transportCost k ν (η x) ∂ρ :=
  OTInfra.mixture k hk ν ρ η
