-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P06.stationaryProcess_strongContinuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:02:27.352555+00:00
-- url     : https://prove2.me/submissions/d512c396-5a92-4a65-950a-993e7deee8be

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P06
noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped Topology ENNReal NNReal

open QAlgorithms.Papers.Independent.Gap48.P06

open scoped symmDiff

theorem g73m_approx {Ω ι : Type*} [MeasurableSpace Ω] (nu : Measure Ω)
    (φ : ι → Ω → Ω) (hφ : ∀ i, MeasurePreserving (φ i) nu nu) (l : Filter ι)
    (A : Set Ω) (hA : MeasurableSet A)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ B, MeasurableSet B ∧ nu (A ∆ B) ≤ ε ∧
      Tendsto (fun i => nu ((φ i ⁻¹' B) ∆ B)) l (𝓝 0)) :
    Tendsto (fun i => nu ((φ i ⁻¹' A) ∆ A)) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : (0 : ℝ≥0∞) < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨B, hB, hAB, hBt⟩ := h (ε / 3) hε3
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hBt) (ε / 3) hε3] with i hi
  have hsub : (φ i ⁻¹' A) ∆ A ⊆ (φ i ⁻¹' (A ∆ B) ∪ ((φ i ⁻¹' B) ∆ B)) ∪ (B ∆ A) := by
    intro x
    simp only [Set.mem_union, Set.mem_symmDiff, Set.mem_preimage]
    tauto
  calc nu ((φ i ⁻¹' A) ∆ A)
      ≤ nu ((φ i ⁻¹' (A ∆ B) ∪ ((φ i ⁻¹' B) ∆ B)) ∪ (B ∆ A)) := measure_mono hsub
    _ ≤ nu (φ i ⁻¹' (A ∆ B)) + nu ((φ i ⁻¹' B) ∆ B) + nu (B ∆ A) := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        rw [(hφ i).measure_preimage (hA.symmDiff hB).nullMeasurableSet, symmDiff_comm B A]
        gcongr
    _ = ε := ENNReal.add_thirds ε

theorem g73m_union {Ω ι : Type*} [MeasurableSpace Ω] (nu : Measure Ω)
    (φ : ι → Ω → Ω) (l : Filter ι) (A B : Set Ω)
    (hA : Tendsto (fun i => nu ((φ i ⁻¹' A) ∆ A)) l (𝓝 0))
    (hB : Tendsto (fun i => nu ((φ i ⁻¹' B) ∆ B)) l (𝓝 0)) :
    Tendsto (fun i => nu ((φ i ⁻¹' (A ∪ B)) ∆ (A ∪ B))) l (𝓝 0) := by
  have hsum : Tendsto (fun i => nu ((φ i ⁻¹' A) ∆ A) + nu ((φ i ⁻¹' B) ∆ B)) l (𝓝 0) := by
    simpa using hA.add hB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hsum (fun _ => bot_le) (fun i => ?_)
  refine (measure_mono ?_).trans (measure_union_le ((φ i ⁻¹' A) ∆ A) ((φ i ⁻¹' B) ∆ B))
  intro x
  simp only [Set.mem_union, Set.mem_symmDiff, Set.mem_preimage]
  tauto

theorem g73m_compl {Ω ι : Type*} [MeasurableSpace Ω] (nu : Measure Ω)
    (φ : ι → Ω → Ω) (l : Filter ι) (A : Set Ω)
    (hA : Tendsto (fun i => nu ((φ i ⁻¹' A) ∆ A)) l (𝓝 0)) :
    Tendsto (fun i => nu ((φ i ⁻¹' Aᶜ) ∆ Aᶜ)) l (𝓝 0) := by
  simpa [Set.preimage_compl, compl_symmDiff_compl] using hA

theorem g73m_iUnion {Ω ι : Type*} [MeasurableSpace Ω] (nu : Measure Ω) [IsFiniteMeasure nu]
    (φ : ι → Ω → Ω) (hφ : ∀ i, MeasurePreserving (φ i) nu nu) (l : Filter ι)
    (f : ℕ → Set Ω) (hfm : ∀ k, MeasurableSet (f k))
    (hf : ∀ k, Tendsto (fun i => nu ((φ i ⁻¹' f k) ∆ f k)) l (𝓝 0)) :
    Tendsto (fun i => nu ((φ i ⁻¹' (⋃ k, f k)) ∆ (⋃ k, f k))) l (𝓝 0) := by
  set B : ℕ → Set Ω := fun n => ⋃ k ∈ Finset.range n, f k with hBdef
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    Finset.measurableSet_biUnion _ (fun k _ => hfm k)
  have hBg : ∀ n, Tendsto (fun i => nu ((φ i ⁻¹' B n) ∆ B n)) l (𝓝 0) := by
    intro n
    induction n with
    | zero => simpa [hBdef] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ≥0∞)) l (𝓝 0))
    | succ n ih =>
      have : B (n + 1) = f n ∪ B n := by
        simp only [hBdef, Finset.range_add_one, Finset.set_biUnion_insert]
      rw [this]
      exact g73m_union nu φ l _ _ (hf n) ih
  have hBsub : ∀ n, B n ⊆ ⋃ k, f k := fun n =>
    Set.iUnion₂_subset fun k _ => Set.subset_iUnion f k
  refine g73m_approx nu φ hφ l _ (MeasurableSet.iUnion hfm) (fun ε hε => ?_)
  have hanti : Antitone (fun n => (⋃ k, f k) \ B n) := by
    intro m n hmn
    apply Set.sdiff_subset_sdiff_right
    exact Set.biUnion_subset_biUnion_left (by simpa using Finset.range_mono hmn)
  have hlim := tendsto_measure_iInter_atTop (μ := nu)
    (fun n => ((MeasurableSet.iUnion hfm).diff (hBm n)).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n, (⋃ k, f k) \ B n) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    rw [Set.mem_iInter] at hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hx 0).1
    refine (hx (k + 1)).2 ?_
    simp only [hBdef, Set.mem_iUnion]
    exact ⟨k, by simp, hk⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 hlim ε hε
  refine ⟨B N, hBm N, ?_, hBg N⟩
  rw [symmDiff_of_ge (hBsub N)]
  exact hN N le_rfl

theorem g73m_conj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (nu : Measure (G → ℝ))
    (hstationary : ∀ g, MeasurePreserving (pathShift g) nu nu)
    (hmeasure : ∀ eps : ℝ, 0 < eps →
      Tendsto (fun g => nu {w | eps ≤ |w g - w 1|}) (𝓝 (1 : G)) (𝓝 0))
    (h : G) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun g => nu {w : G → ℝ | δ ≤ |w (g * h) - w h|}) (𝓝 1) (𝓝 0) := by
  have heq : ∀ g : G, {w : G → ℝ | δ ≤ |w (g * h) - w h|} =
      pathShift h⁻¹ ⁻¹' {w | δ ≤ |w (h⁻¹ * g * h) - w 1|} := by
    intro g; ext w; simp [pathShift, mul_assoc]
  have hmeas : ∀ g : G, MeasurableSet {w : G → ℝ | δ ≤ |w (h⁻¹ * g * h) - w 1|} := by
    intro g
    have hm : Measurable fun w : G → ℝ => |w (h⁻¹ * g * h) - w 1| := by fun_prop
    exact measurableSet_le measurable_const hm
  have hc : Tendsto (fun g : G => h⁻¹ * g * h) (𝓝 1) (𝓝 1) := by
    have hcont : Continuous (fun g : G => h⁻¹ * g * h) := by fun_prop
    simpa using hcont.tendsto 1
  have := (hmeasure δ hδ).comp hc
  refine this.congr fun g => ?_
  simp only [Function.comp]
  rw [heq g, (hstationary h⁻¹).measure_preimage (hmeas g).nullMeasurableSet]

theorem g73m_open {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (nu : Measure (G → ℝ)) [IsProbabilityMeasure nu]
    (hstationary : ∀ g, MeasurePreserving (pathShift g) nu nu)
    (hmeasure : ∀ eps : ℝ, 0 < eps →
      Tendsto (fun g => nu {w | eps ≤ |w g - w 1|}) (𝓝 (1 : G)) (𝓝 0))
    (s : Finset G) (S : Set (s → ℝ)) (hS : IsOpen S) :
    Tendsto (fun g : G => nu ((pathShift g⁻¹ ⁻¹' MeasureTheory.cylinder s S) ∆
      MeasureTheory.cylinder s S)) (𝓝 1) (𝓝 0) := by
  by_cases hSc : (Sᶜ).Nonempty
  swap
  · have hSu : S = Set.univ := by
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hSc
      exact hSc
    subst hSu
    simpa [MeasureTheory.cylinder] using
      (tendsto_const_nhds : Tendsto (fun _ : G => (0 : ℝ≥0∞)) (𝓝 1) (𝓝 0))
  set D : ℕ → Set (s → ℝ) := fun n => S ∩ {x | Metric.infDist x Sᶜ < 1 / ((n : ℝ) + 1)}
    with hDdef
  have hDm : ∀ n, MeasurableSet (D n) := fun n =>
    hS.measurableSet.inter (measurableSet_lt (Metric.continuous_infDist_pt _).measurable
      measurable_const)
  have hanti : Antitone (fun n => MeasureTheory.cylinder (α := fun _ : G => ℝ) s (D n)) := by
    intro m n hmn w hw
    simp only [MeasureTheory.mem_cylinder, hDdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hw ⊢
    refine ⟨hw.1, hw.2.trans_le ?_⟩
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hlim := tendsto_measure_iInter_atTop (μ := nu)
    (fun n => ((hDm n).cylinder (α := fun _ : G => ℝ) s).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ n, MeasureTheory.cylinder (α := fun _ : G => ℝ) s (D n)) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun w hw => ?_
    rw [Set.mem_iInter] at hw
    have h0 := hw 0
    simp only [MeasureTheory.mem_cylinder, hDdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at h0
    have hzero : Metric.infDist (s.restrict w) Sᶜ = 0 := by
      refine le_antisymm ?_ Metric.infDist_nonneg
      by_contra hpos
      push Not at hpos
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      have hn' := hw n
      simp only [MeasureTheory.mem_cylinder, hDdef, Set.mem_inter_iff, Set.mem_ofPred_eq] at hn'
      linarith [hn'.2]
    have hcl : s.restrict w ∈ closure Sᶜ := (Metric.mem_closure_iff_infDist_zero hSc).2 hzero
    rw [hS.isClosed_compl.closure_eq] at hcl
    exact hcl h0.1
  rw [hempty, measure_empty] at hlim
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : (0 : ℝ≥0∞) < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 hlim (ε / 3) hε3
  have hND := hN N le_rfl
  simp only [Function.comp] at hND
  set δ : ℝ := 1 / ((N : ℝ) + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hsum : Tendsto (fun g : G => ∑ i ∈ s, nu {w : G → ℝ | δ ≤ |w (g * i) - w i|})
      (𝓝 1) (𝓝 0) := by
    have := tendsto_finsetSum s (fun i _ => g73m_conj nu hstationary hmeasure i δ hδ)
    simpa using this
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hsum) (ε / 3) hε3] with g hg
  have hsub : (pathShift g⁻¹ ⁻¹' MeasureTheory.cylinder s S) ∆ MeasureTheory.cylinder s S ⊆
      ((⋃ i ∈ s, {w : G → ℝ | δ ≤ |w (g * i) - w i|}) ∪
        MeasureTheory.cylinder (α := fun _ : G => ℝ) s (D N)) ∪
        pathShift g⁻¹ ⁻¹' MeasureTheory.cylinder (α := fun _ : G => ℝ) s (D N) := by
    intro w hw
    by_cases hclose : ∀ i ∈ s, |w (g * i) - w i| < δ
    · have hdist : dist (s.restrict (pathShift g⁻¹ w)) (s.restrict w) < δ := by
        rw [dist_pi_lt_iff hδ]
        intro b
        simp only [Finset.restrict, pathShift, inv_inv, Real.dist_eq]
        exact hclose b b.2
      have hw' : (s.restrict (pathShift g⁻¹ w) ∈ S ∧ s.restrict w ∉ S) ∨
          (s.restrict w ∈ S ∧ s.restrict (pathShift g⁻¹ w) ∉ S) := by
        simp only [Set.mem_symmDiff, Set.mem_preimage, MeasureTheory.mem_cylinder] at hw
        tauto
      rcases hw' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        simp only [Set.mem_preimage, MeasureTheory.mem_cylinder, hDdef, Set.mem_inter_iff,
          Set.mem_ofPred_eq]
        refine ⟨h1, ?_⟩
        exact (Metric.infDist_le_dist_of_mem (Set.mem_compl h2)).trans_lt hdist
      · left; right
        simp only [MeasureTheory.mem_cylinder, hDdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
        refine ⟨h1, ?_⟩
        rw [dist_comm] at hdist
        exact (Metric.infDist_le_dist_of_mem (Set.mem_compl h2)).trans_lt hdist
    · push Not at hclose
      obtain ⟨i, hi, hi'⟩ := hclose
      left; left
      exact Set.mem_biUnion hi hi'
  calc nu ((pathShift g⁻¹ ⁻¹' MeasureTheory.cylinder s S) ∆ MeasureTheory.cylinder s S)
      ≤ nu (((⋃ i ∈ s, {w : G → ℝ | δ ≤ |w (g * i) - w i|}) ∪
        MeasureTheory.cylinder (α := fun _ : G => ℝ) s (D N)) ∪
        pathShift g⁻¹ ⁻¹' MeasureTheory.cylinder (α := fun _ : G => ℝ) s (D N)) := measure_mono hsub
    _ ≤ (∑ i ∈ s, nu {w : G → ℝ | δ ≤ |w (g * i) - w i|}) +
          nu (MeasureTheory.cylinder (α := fun _ : G => ℝ) s (D N)) +
          nu (pathShift g⁻¹ ⁻¹' MeasureTheory.cylinder (α := fun _ : G => ℝ) s (D N)) := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_biUnion_finset_le _ _
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        rw [(hstationary g⁻¹).measure_preimage ((hDm N).cylinder (α := fun _ : G => ℝ) s).nullMeasurableSet]
        gcongr
    _ = ε := ENNReal.add_thirds ε

theorem g73m_cyl {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (nu : Measure (G → ℝ)) [IsProbabilityMeasure nu]
    (hstationary : ∀ g, MeasurePreserving (pathShift g) nu nu)
    (hmeasure : ∀ eps : ℝ, 0 < eps →
      Tendsto (fun g => nu {w | eps ≤ |w g - w 1|}) (𝓝 (1 : G)) (𝓝 0))
    (s : Finset G) : ∀ (S : Set (s → ℝ)), MeasurableSet S →
    Tendsto (fun g : G => nu ((pathShift g⁻¹ ⁻¹' MeasureTheory.cylinder s S) ∆
      MeasureTheory.cylinder s S)) (𝓝 1) (𝓝 0) := by
  intro S hS
  refine MeasurableSpace.induction_on_inter
    (C := fun S _ => Tendsto (fun g : G => nu ((pathShift g⁻¹ ⁻¹'
      MeasureTheory.cylinder (α := fun _ : G => ℝ) s S) ∆
      MeasureTheory.cylinder (α := fun _ : G => ℝ) s S)) (𝓝 1) (𝓝 0))
    (s := {U : Set (s → ℝ) | IsOpen U}) BorelSpace.measurable_eq isPiSystem_isOpen
    ?_ ?_ ?_ ?_ S hS
  · simpa [MeasureTheory.cylinder_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : G => (0 : ℝ≥0∞)) (𝓝 1) (𝓝 0))
  · intro t ht
    exact g73m_open nu hstationary hmeasure s t ht
  · intro t _ ht
    rw [← MeasureTheory.compl_cylinder]
    exact g73m_compl nu _ _ _ ht
  · intro f _ hfm hf
    have heq : MeasureTheory.cylinder (α := fun _ : G => ℝ) s (⋃ i, f i) =
        ⋃ i, MeasureTheory.cylinder (α := fun _ : G => ℝ) s (f i) := by
      simp [MeasureTheory.cylinder, Set.preimage_iUnion]
    rw [heq]
    exact g73m_iUnion nu (fun g : G => pathShift g⁻¹) (fun g => hstationary g⁻¹) _ _
      (fun i => (hfm i).cylinder s) hf

theorem g73m_all {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (nu : Measure (G → ℝ)) [IsProbabilityMeasure nu]
    (hstationary : ∀ g, MeasurePreserving (pathShift g) nu nu)
    (hmeasure : ∀ eps : ℝ, 0 < eps →
      Tendsto (fun g => nu {w | eps ≤ |w g - w 1|}) (𝓝 (1 : G)) (𝓝 0)) :
    ∀ (A : Set (G → ℝ)), MeasurableSet A →
    Tendsto (fun g : G => nu ((pathShift g⁻¹ ⁻¹' A) ∆ A)) (𝓝 1) (𝓝 0) := by
  intro A hA
  refine MeasurableSpace.induction_on_inter
    (C := fun A _ => Tendsto (fun g : G => nu ((pathShift g⁻¹ ⁻¹' A) ∆ A)) (𝓝 1) (𝓝 0))
    (s := MeasureTheory.measurableCylinders (fun _ : G => ℝ))
    MeasureTheory.generateFrom_measurableCylinders.symm
    MeasureTheory.isPiSystem_measurableCylinders ?_ ?_ ?_ ?_ A hA
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : G => (0 : ℝ≥0∞)) (𝓝 1) (𝓝 0))
  · intro t ht
    obtain ⟨s, S, hS, rfl⟩ := (MeasureTheory.mem_measurableCylinders t).1 ht
    exact g73m_cyl nu hstationary hmeasure s S hS
  · intro t _ ht
    exact g73m_compl nu _ _ _ ht
  · intro f _ hfm hf
    exact g73m_iUnion nu (fun g : G => pathShift g⁻¹) (fun g => hstationary g⁻¹) _ _ hfm hf

theorem g73m_congr {Ω : Type*} [MeasurableSpace Ω] (nu : Measure Ω)
    (φ ψ : Ω → Ω) (hφ : MeasurePreserving φ nu nu) (hψ : MeasurePreserving ψ nu nu)
    (h : φ = ψ) (f : Lp ℂ 2 nu) :
    Lp.compMeasurePreserving φ hφ f = Lp.compMeasurePreserving ψ hψ f := by
  subst h; rfl

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (nu : Measure (G → ℝ)) [IsProbabilityMeasure nu]
    (hstationary : ∀ g, MeasurePreserving (pathShift g) nu nu)
    (hmeasure : ∀ eps : ℝ, 0 < eps →
      Tendsto (fun g => nu {w | eps ≤ |w g - w 1|}) (𝓝 (1 : G)) (𝓝 0)) :
    ∀ f, Continuous (fun g => pathKoopman nu hstationary g f) := by
  have hEq : Equicontinuous (fun (g : G) (f : Lp ℂ 2 nu) => pathKoopman nu hstationary g f) := by
    refine Metric.equicontinuous_of_continuity_modulus id tendsto_id _ (fun x y g => ?_)
    simp only [pathKoopman, id]
    exact ((Lp.isometry_compMeasurePreserving (hstationary g⁻¹)).dist_eq x y).le
  have hV : ∀ f : Lp ℂ 2 nu,
      Tendsto (fun g => pathKoopman nu hstationary g f) (𝓝 1) (𝓝 f) := by
    intro f
    refine Lp.induction (p := 2) (by norm_num)
      (fun f => Tendsto (fun g => pathKoopman nu hstationary g f) (𝓝 1) (𝓝 f)) ?_ ?_ ?_ f
    · intro c A hA hμA
      simp only [Lp.simpleFunc.coe_indicatorConst, pathKoopman,
        Lp.indicatorConstLp_compMeasurePreserving]
      exact tendsto_indicatorConstLp_set (by norm_num)
        (g73m_all nu hstationary hmeasure A hA)
    · intro f1 f2 _ _ _ h1 h2
      have := h1.add h2
      simpa [pathKoopman, map_add] using this
    · have := Equicontinuous.isClosed_setOfPred_tendsto (l := 𝓝 (1 : G)) hEq continuous_id
      simpa using this
  intro f
  rw [continuous_iff_continuousAt]
  intro g0
  have hcomp : ∀ g, pathKoopman nu hstationary g f =
      pathKoopman nu hstationary g0 (pathKoopman nu hstationary (g0⁻¹ * g) f) := by
    intro g
    simp only [pathKoopman]
    rw [← Lp.compMeasurePreserving_comp_apply]
    apply g73m_congr
    funext w x
    simp [pathShift, mul_assoc]
  have hc : Tendsto (fun g : G => g0⁻¹ * g) (𝓝 g0) (𝓝 1) := by
    have hcont : Continuous (fun g : G => g0⁻¹ * g) := by fun_prop
    simpa using hcont.tendsto g0
  have hU : Continuous (pathKoopman nu hstationary g0) :=
    (Lp.isometry_compMeasurePreserving (hstationary g0⁻¹)).continuous
  have := (hU.tendsto f).comp ((hV f).comp hc)
  exact this.congr fun g => (hcomp g).symm

end
