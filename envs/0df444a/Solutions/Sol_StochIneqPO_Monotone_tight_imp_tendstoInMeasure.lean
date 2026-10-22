-- Prove2me | solution 1 for StochIneqPO.Monotone.tight_imp_tendstoInMeasure
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:42:56.908803+00:00
-- url     : https://prove2.me/submissions/c04784b8-20d3-47f5-80c3-ba5e3c91c9fa

import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_ConvergenceModes



namespace StochIneqPO.Monotone

open MeasureTheory Filter Topology
open scoped ENNReal

theorem mem_of_mapClusterPt' {X ι : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClosed S)
    {F : Filter ι} {u : ι → X} {x : X} (h : MapClusterPt x F u) (hev : ∀ᶠ i in F, u i ∈ S) :
    x ∈ S := by
  by_contra hx
  have := (mapClusterPt_iff_frequently.1 h) Sᶜ (hS.isOpen_compl.mem_nhds hx)
  obtain ⟨i, hi1, hi2⟩ := (this.and_eventually hev).exists
  exact hi1 hi2

theorem cluster_le {E : Type*} [TopologicalSpace E] [PartialOrder E] [OrderClosedTopology E]
    {f : ℕ → E} (hf : Monotone f) {a b : E} (ha : MapClusterPt a atTop f)
    (hb : MapClusterPt b atTop f) : a ≤ b := by
  have h1 : ∀ k, f k ≤ b := fun k =>
    mem_of_mapClusterPt' (S := Set.Ici (f k)) isClosed_Ici hb
      (eventually_atTop.2 ⟨k, fun m hm => hf hm⟩)
  exact mem_of_mapClusterPt' (S := Set.Iic b) isClosed_Iic ha (Eventually.of_forall h1)

theorem cluster_unique {E : Type*} [TopologicalSpace E] [PartialOrder E] [OrderClosedTopology E]
    {f : ℕ → E} (hf : Monotone f) {a b : E} (ha : MapClusterPt a atTop f)
    (hb : MapClusterPt b atTop f) : a = b :=
  le_antisymm (cluster_le hf ha hb) (cluster_le hf hb ha)

theorem cauchy_in_measure {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i)) (hmono : ∀ ω, Monotone fun i => X i ω)
    (htight : LawsTight μ X) (δ : ℝ) (hδ : 0 < δ) (ρ : ℝ≥0∞) (hρ : 0 < ρ) (hρ' : ρ ≠ ⊤) :
    ∃ N, ∀ i ≥ N, ∀ j ≥ N, μ {ω | δ ≤ dist (X i ω) (X j ω)} ≤ 4 * ρ := by
  by_contra hcon
  push_neg at hcon
  choose I hI J hJ hμ using hcon
  obtain ⟨K, hK, hKμ⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 htight) ρ hρ
  have hKi : ∀ i, μ (X i ⁻¹' Kᶜ) ≤ ρ := by
    intro i
    have := hKμ (μ.map (X i)) ⟨i, rfl⟩
    rwa [Measure.map_apply (hX i) hK.isClosed.measurableSet.compl] at this
  let B : ℕ → Set Ω := fun k =>
    X (I k) ⁻¹' K ∩ X (J k) ⁻¹' K ∩ {ω | δ ≤ dist (X (I k) ω) (X (J k) ω)}
  have hBmeas : ∀ k, MeasurableSet (B k) := by
    intro k
    exact ((hX (I k) hK.isClosed.measurableSet).inter (hX (J k) hK.isClosed.measurableSet)).inter
      (measurableSet_le measurable_const ((hX (I k)).dist (hX (J k))))
  have hBlow : ∀ k, 2 * ρ ≤ μ (B k) := by
    intro k
    have hsub : {ω | δ ≤ dist (X (I k) ω) (X (J k) ω)} ⊆
        B k ∪ X (I k) ⁻¹' Kᶜ ∪ X (J k) ⁻¹' Kᶜ := by
      intro ω hω
      by_cases h1 : X (I k) ω ∈ K
      · by_cases h2 : X (J k) ω ∈ K
        · exact Or.inl (Or.inl ⟨⟨h1, h2⟩, hω⟩)
        · exact Or.inr h2
      · exact Or.inl (Or.inr h1)
    have h3 : μ {ω | δ ≤ dist (X (I k) ω) (X (J k) ω)} ≤ μ (B k) + ρ + ρ :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans
        (add_le_add ((measure_union_le _ _).trans (add_le_add le_rfl (hKi _))) (hKi _)))
    have h4 : 2 * ρ + 2 * ρ ≤ μ (B k) + 2 * ρ := by
      calc 2 * ρ + 2 * ρ = 4 * ρ := by ring
        _ ≤ μ {ω | δ ≤ dist (X (I k) ω) (X (J k) ω)} := (hμ k).le
        _ ≤ μ (B k) + ρ + ρ := h3
        _ = μ (B k) + 2 * ρ := by ring
    exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by norm_num) hρ')).1 h4
  let T : ℕ → Set Ω := fun N => ⋃ k, ⋃ (_ : N ≤ k), B k
  have hTanti : Antitone T := by
    intro N M hNM
    exact Set.iUnion₂_mono' fun k hk => ⟨k, hNM.trans hk, subset_rfl⟩
  have hTmeas : ∀ N, MeasurableSet (T N) := fun N =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hBmeas k
  have hTlow : ∀ N, 2 * ρ ≤ μ (T N) := fun N =>
    (hBlow N).trans (measure_mono (Set.subset_iUnion₂ (s := fun k (_ : N ≤ k) => B k) N le_rfl))
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun N => (hTmeas N).nullMeasurableSet) hTanti
    ⟨0, measure_ne_top _ _⟩
  have hge : 2 * ρ ≤ μ (⋂ N, T N) := ge_of_tendsto hlim (Eventually.of_forall hTlow)
  have hempty : (⋂ N, T N) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hω
    have hfreq : ∃ᶠ k in atTop, ω ∈ B k := by
      rw [frequently_atTop]
      intro N
      have := hω N
      simp only [T, Set.mem_iUnion] at this
      obtain ⟨k, hk, hk'⟩ := this
      exact ⟨k, hk, hk'⟩
    let S : Set (E × E) := (K ×ˢ K) ∩ {p | δ ≤ dist p.1 p.2}
    have hSc : IsCompact S :=
      (hK.prod hK).inter_right (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
    have hfreq2 : ∃ᶠ k in atTop, (X (I k) ω, X (J k) ω) ∈ S := by
      refine hfreq.mono fun k hk => ?_
      exact ⟨⟨hk.1.1, hk.1.2⟩, hk.2⟩
    obtain ⟨p, hpS, hp⟩ := hSc.exists_mapClusterPt_of_frequently hfreq2
    have hI' : Tendsto I atTop atTop :=
      tendsto_atTop_mono hI tendsto_id
    have hJ' : Tendsto J atTop atTop :=
      tendsto_atTop_mono hJ tendsto_id
    have hpa : MapClusterPt p.1 atTop (fun m => X m ω) := by
      have h1 : MapClusterPt p.1 atTop (Prod.fst ∘ fun k => (X (I k) ω, X (J k) ω)) :=
        hp.tendsto_comp continuous_fst.continuousAt
      have h2 : ClusterPt p.1 (map (fun k => X (I k) ω) atTop) := h1
      refine ClusterPt.mono (f := map (fun k => X (I k) ω) atTop) h2 ?_
      have e : map (fun k => X (I k) ω) atTop = map (fun m => X m ω) (map I atTop) :=
        by rw [Filter.map_map]; rfl
      rw [e]
      exact map_mono hI'
    have hpb : MapClusterPt p.2 atTop (fun m => X m ω) := by
      have h1 : MapClusterPt p.2 atTop (Prod.snd ∘ fun k => (X (I k) ω, X (J k) ω)) :=
        hp.tendsto_comp continuous_snd.continuousAt
      have h2 : ClusterPt p.2 (map (fun k => X (J k) ω) atTop) := h1
      refine ClusterPt.mono (f := map (fun k => X (J k) ω) atTop) h2 ?_
      have e : map (fun k => X (J k) ω) atTop = map (fun m => X m ω) (map J atTop) :=
        by rw [Filter.map_map]; rfl
      rw [e]
      exact map_mono hJ'
    have heq := cluster_unique (hmono ω) hpa hpb
    have := hpS.2
    simp only [Set.mem_setOf_eq] at this
    rw [heq, dist_self] at this
    linarith
  rw [hempty, measure_empty] at hge
  have : 0 < 2 * ρ := by
    apply ENNReal.mul_pos (by norm_num) hρ.ne'
  exact absurd hge (not_le.2 this)


theorem cauchy_in_measure_real {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i)) (hmono : ∀ ω, Monotone fun i => X i ω)
    (htight : LawsTight μ X) (δ : ℝ) (hδ : 0 < δ) (η : ℝ) (hη : 0 < η) :
    ∃ N, ∀ i ≥ N, ∀ j ≥ N, μ {ω | δ ≤ dist (X i ω) (X j ω)} ≤ ENNReal.ofReal η := by
  obtain ⟨N, hN⟩ := cauchy_in_measure μ X hX hmono htight δ hδ (ENNReal.ofReal (η / 4))
    (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_ne_top
  refine ⟨N, fun i hi j hj => (hN i hi j hj).trans (le_of_eq ?_)⟩
  rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

theorem tendstoInMeasure_of_cim {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i))
    (hC : ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
      ∃ N, ∀ i ≥ N, ∀ j ≥ N, μ {ω | δ ≤ dist (X i ω) (X j ω)} ≤ ENNReal.ofReal η) :
    ∃ Y : Ω → E, Measurable Y ∧ TendstoInMeasure μ X atTop Y := by
  classical
  have hpos : ∀ k : ℕ, (0:ℝ) < (1/2) ^ k := fun k => by positivity
  choose N hN using fun k : ℕ => hC ((1/2) ^ k) (hpos k) ((1/2) ^ k) (hpos k)
  let n : ℕ → ℕ := fun k => k + (Finset.range (k + 1)).sup N
  have hnN : ∀ k j, j ≤ k → N j ≤ n k := by
    intro k j hj
    have : N j ≤ (Finset.range (k + 1)).sup N :=
      Finset.le_sup (f := N) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    show N j ≤ k + (Finset.range (k + 1)).sup N
    omega
  have hnk : ∀ k, k ≤ n k := fun k => Nat.le_add_right _ _
  have hn_tend : Tendsto n atTop atTop := tendsto_atTop_mono hnk tendsto_id
  let Ek : ℕ → Set Ω := fun k => {ω | (1/2:ℝ) ^ k ≤ dist (X (n k) ω) (X (n (k + 1)) ω)}
  have hEk : ∀ k, μ (Ek k) ≤ ENNReal.ofReal ((1/2) ^ k) := fun k =>
    hN k (n k) (hnN k k le_rfl) (n (k + 1)) (hnN (k + 1) k (Nat.le_succ k))
  have hsum : ∑' k, μ (Ek k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, ENNReal.ofReal ((1/2:ℝ) ^ k)) ?_ (ENNReal.tsum_le_tsum hEk)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (hpos k).le) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  have hae1 := ae_eventually_notMem hsum
  have hae2 : ∀ᵐ ω ∂μ, ∃ L, Tendsto (fun k => X (n k) ω) atTop (𝓝 L) := by
    filter_upwards [hae1] with ω hω
    have hs : Summable (fun k => dist (X (n k) ω) (X (n (k + 1)) ω)) := by
      refine Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => (1/2:ℝ) ^ k)
        summable_geometric_two ?_
      filter_upwards [hω] with k hk
      simp only [Ek, Set.mem_setOf_eq, not_le] at hk
      rw [Real.norm_of_nonneg dist_nonneg]
      exact hk.le
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hs)
  let g : Ω → E := fun ω =>
    if h : ∃ L, Tendsto (fun k => X (n k) ω) atTop (𝓝 L) then h.choose else X 0 ω
  have hg : ∀ᵐ ω ∂μ, Tendsto (fun k => X (n k) ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hae2] with ω hω
    simp only [g, dif_pos hω]
    exact hω.choose_spec
  have hgm : AEMeasurable g μ :=
    aemeasurable_of_tendsto_metrizable_ae' (fun k => (hX (n k)).aemeasurable) hg
  refine ⟨hgm.mk g, hgm.measurable_mk, ?_⟩
  have hgY : ∀ᵐ ω ∂μ, Tendsto (fun k => X (n k) ω) atTop (𝓝 (hgm.mk g ω)) := by
    filter_upwards [hg, hgm.ae_eq_mk] with ω h1 h2
    rwa [← h2]
  have hsub : TendstoInMeasure μ (fun k => X (n k)) atTop (hgm.mk g) :=
    tendstoInMeasure_of_tendsto_ae (fun k => (hX (n k)).aestronglyMeasurable) hgY
  rw [tendstoInMeasure_iff_dist] at hsub ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro θ hθ
  by_cases hθt : θ = ⊤
  · exact ⟨0, fun _ _ => by simp [hθt]⟩
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 < t ∧ θ = ENNReal.ofReal t :=
    ⟨θ.toReal, ENNReal.toReal_pos hθ.ne' hθt, (ENNReal.ofReal_toReal hθt).symm⟩
  obtain ⟨N1, hN1⟩ := hC (ε / 2) (by positivity) (t / 2) (by positivity)
  have h2 := ENNReal.tendsto_atTop_zero.1 (hsub (ε / 2) (by positivity)) (ENNReal.ofReal (t / 2))
    (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨K0, hK0⟩ := h2
  set k := max K0 N1 with hk
  have hk1 : K0 ≤ k := le_max_left _ _
  have hk2 : N1 ≤ n k := (le_max_right _ _).trans (hnk k)
  refine ⟨N1, fun i hi => ?_⟩
  have hsubset : {ω | ε ≤ dist (X i ω) (hgm.mk g ω)} ⊆
      {ω | ε / 2 ≤ dist (X i ω) (X (n k) ω)} ∪ {ω | ε / 2 ≤ dist (X (n k) ω) (hgm.mk g ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
    have := dist_triangle (X i ω) (X (n k) ω) (hgm.mk g ω)
    linarith [hnot.1, hnot.2]
  calc μ {ω | ε ≤ dist (X i ω) (hgm.mk g ω)}
      ≤ μ ({ω | ε / 2 ≤ dist (X i ω) (X (n k) ω)} ∪
          {ω | ε / 2 ≤ dist (X (n k) ω) (hgm.mk g ω)}) := measure_mono hsubset
    _ ≤ μ {ω | ε / 2 ≤ dist (X i ω) (X (n k) ω)} + μ {ω | ε / 2 ≤ dist (X (n k) ω) (hgm.mk g ω)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) :=
        add_le_add (hN1 i hi (n k) hk2) (hK0 k hk1)
    _ = ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

theorem tight_imp_tendstoInMeasure_core {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i)) (hmono : ∀ ω, Monotone fun i => X i ω)
    (htight : LawsTight μ X) :
    ConvergesInProbability μ X :=
  tendstoInMeasure_of_cim μ X hX (fun δ hδ η hη => cauchy_in_measure_real μ X hX hmono htight δ hδ η hη)

end StochIneqPO.Monotone

open StochIneqPO.Monotone
open MeasureTheory

theorem solution {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i)) (hmono : ∀ ω, Monotone fun i => X i ω)
    (htight : LawsTight μ X) :
    ConvergesInProbability μ X := by
  exact tight_imp_tendstoInMeasure_core μ X hX hmono htight
