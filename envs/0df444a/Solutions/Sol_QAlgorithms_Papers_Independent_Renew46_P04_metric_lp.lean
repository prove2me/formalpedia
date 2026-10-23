-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.metric_lp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:42:20.848881+00:00
-- url     : https://prove2.me/submissions/b5d63f5e-cd0e-4d98-871c-d711d7d579b6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04

noncomputable section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace X7M2

variable {K : Type*} [RCLike K] {A : Type*} (m : MeasurableSpace A) [m0 : MeasurableSpace A] {μ : Measure A}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem X7M2_ind_ae {T : Set A} (hT : MeasurableSet T) {F u : A → K}
    (h : F =ᵐ[μ.restrict T] u) : T.indicator F =ᵐ[μ] T.indicator u := by
  have := (ae_restrict_iff' hT).1 h
  filter_upwards [this] with a ha
  by_cases haT : a ∈ T
  · simp [Set.indicator_of_mem haT, ha haT]
  · simp [Set.indicator_of_notMem haT]

theorem X7M2_mem (T : Set A) (hT : MeasurableSet T)
    [IsFiniteMeasure (μ.restrict T)] (f : Lp K p μ) :
    MemLp (T.indicator ((μ.restrict T)[(f : A → K) | m])) p μ :=
  (memLp_indicator_iff_restrict hT).2 (((Lp.memLp f).restrict T).condExp Fact.out)

theorem X7M2_int (T : Set A) [IsFiniteMeasure (μ.restrict T)] (f : Lp K p μ) :
    Integrable (f : A → K) (μ.restrict T) :=
  ((Lp.memLp f).restrict T).integrable Fact.out

/-- averaging projection: conditional expectation on `T`, extended by zero. -/
def X7M2_P (T : Set A) (hT : MeasurableSet T)
    [IsFiniteMeasure (μ.restrict T)] : Lp K p μ →L[K] Lp K p μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (X7M2_mem m T hT f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (X7M2_mem m T hT (f + g)),
          MemLp.coeFn_toLp (X7M2_mem m T hT f), MemLp.coeFn_toLp (X7M2_mem m T hT g),
          Lp.coeFn_add ((X7M2_mem m T hT f).toLp _) ((X7M2_mem m T hT g).toLp _),
          X7M2_ind_ae hT ((condExp_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))).trans
            (condExp_add (X7M2_int T f) (X7M2_int T g) m))] with a h1 h2 h3 h4 h5
        rw [h4, Pi.add_apply, h1, h2, h3, h5]
        by_cases haT : a ∈ T
        · simp [Set.indicator_of_mem haT]
        · simp [Set.indicator_of_notMem haT]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (X7M2_mem m T hT (c • f)),
          MemLp.coeFn_toLp (X7M2_mem m T hT f),
          Lp.coeFn_smul c ((X7M2_mem m T hT f).toLp _),
          X7M2_ind_ae hT ((condExp_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))).trans
            (condExp_smul c (f : A → K) m))] with a h1 h2 h3 h5
        rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2, h5]
        by_cases haT : a ∈ T
        · simp [Set.indicator_of_mem haT]
        · simp [Set.indicator_of_notMem haT] }
    1 (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [Lp.norm_toLp, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hT]
      exact (eLpNorm_condExp_le_eLpNorm _ Fact.out).trans (eLpNorm_restrict_le _ _ _ _))

theorem X7M2_P_ae (T : Set A) (hT : MeasurableSet T)
    [IsFiniteMeasure (μ.restrict T)] (f : Lp K p μ) :
    (X7M2_P m T hT f : A → K) =ᵐ[μ] T.indicator ((μ.restrict T)[(f : A → K) | m]) :=
  MemLp.coeFn_toLp (X7M2_mem m T hT f)

theorem X7M2_P_fix (T : Set A) (hT : MeasurableSet T) (hm : m ≤ m0)
    [IsFiniteMeasure (μ.restrict T)] (f : Lp K p μ) (u : A → K)
    (hu : StronglyMeasurable[m] u) (hui : Integrable u (μ.restrict T))
    (hf : (f : A → K) =ᵐ[μ] T.indicator u) :
    (X7M2_P m T hT f : A → K) =ᵐ[μ] T.indicator u := by
  refine (X7M2_P_ae m T hT f).trans (X7M2_ind_ae hT ?_)
  have h1 : (f : A → K) =ᵐ[μ.restrict T] u :=
    Filter.EventuallyEq.trans (ae_restrict_of_ae hf) (indicator_ae_eq_restrict hT)
  refine (condExp_congr_ae h1).trans ?_
  rw [condExp_of_stronglyMeasurable hm hu hui]

theorem X7M2_P_idem (T : Set A) (hT : MeasurableSet T) (hm : m ≤ m0)
    [IsFiniteMeasure (μ.restrict T)] :
    (X7M2_P (K := K) (p := p) (μ := μ) m T hT).comp (X7M2_P m T hT) = X7M2_P m T hT := by
  ext1 f
  apply Lp.ext
  exact (X7M2_P_fix m T hT hm _ _ stronglyMeasurable_condExp integrable_condExp
    (X7M2_P_ae m T hT f)).trans (X7M2_P_ae m T hT f).symm

theorem X7M2_P_fd {ι : Type*} [Fintype ι] (G : A → (ι → K)) (hG : Measurable G)
    (hfin : (Set.range G).Finite) (T : Set A) (hT : MeasurableSet T) (hTμ : μ T < ∞)
    [IsFiniteMeasure (μ.restrict T)] :
    FiniteDimensional K (X7M2_P (K := K) (p := p) (μ := μ) (MeasurableSpace.comap G inferInstance)
      T hT).range := by
  classical
  haveI : Finite (Set.range G) := hfin.to_subtype
  haveI : Fintype (Set.range G) := Fintype.ofFinite _
  set S : Set.range G → Set A := fun r => T ∩ G ⁻¹' {r.1} with hSdef
  have hS : ∀ r, MeasurableSet (S r) := fun r => hT.inter (hG (measurableSet_singleton _))
  have hSμ : ∀ r, μ (S r) ≠ ∞ := fun r =>
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hTμ).ne
  let F : (Set.range G → K) → A → K := fun ψ => ∑ r, ψ r • (S r).indicator (fun _ => (1 : K))
  have hF : ∀ ψ, MemLp (F ψ) p μ := fun ψ =>
    memLp_finsetSum' _ (fun r _ =>
      (memLp_indicator_const p (hS r) (1 : K) (Or.inr (hSμ r))).const_smul (ψ r))
  let L : (Set.range G → K) →ₗ[K] Lp K p μ :=
    { toFun := fun ψ => (hF ψ).toLp _
      map_add' := fun ψ φ => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (hF (ψ + φ)), MemLp.coeFn_toLp (hF ψ),
          MemLp.coeFn_toLp (hF φ), Lp.coeFn_add ((hF ψ).toLp _) ((hF φ).toLp _)]
          with a h1 h2 h3 h4
        rw [h4, Pi.add_apply, h1, h2, h3]
        simp only [F, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, add_smul,
          Finset.sum_add_distrib]
      map_smul' := fun c ψ => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (hF (c • ψ)), MemLp.coeFn_toLp (hF ψ),
          Lp.coeFn_smul c ((hF ψ).toLp _)] with a h1 h2 h3
        rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2]
        simp only [F, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
        rw [Finset.mul_sum] }
  have hle : (X7M2_P (K := K) (p := p) (μ := μ) (MeasurableSpace.comap G inferInstance) T hT).range ≤
      LinearMap.range L := by
    rintro _ ⟨f, rfl⟩
    set h := (μ.restrict T)[(f : A → K) | MeasurableSpace.comap G inferInstance] with hh
    have hfac : h.FactorsThrough G := StronglyMeasurable.factorsThrough stronglyMeasurable_condExp
    let φ := Function.extend G h 0
    refine ⟨fun r => φ r.1, ?_⟩
    apply Lp.ext
    refine (MemLp.coeFn_toLp (hF _)).trans (EventuallyEq.trans ?_ (X7M2_P_ae _ T hT f).symm)
    refine Eventually.of_forall fun a => ?_
    simp only [F, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single ⟨G a, Set.mem_range_self a⟩]
    · by_cases haT : a ∈ T
      · have : a ∈ S ⟨G a, Set.mem_range_self a⟩ := ⟨haT, rfl⟩
        rw [Set.indicator_of_mem this, Set.indicator_of_mem haT, mul_one]
        exact hfac.extend_apply 0 a
      · have : a ∉ S ⟨G a, Set.mem_range_self a⟩ := fun h' => haT h'.1
        rw [Set.indicator_of_notMem this, Set.indicator_of_notMem haT, mul_zero]
    · intro r _ hr
      have : a ∉ S r := fun h' => hr (Subtype.ext h'.2.symm)
      rw [Set.indicator_of_notMem this, mul_zero]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  haveI : FiniteDimensional K (LinearMap.range L) := LinearMap.finiteDimensional_range L
  exact Submodule.finiteDimensional_of_le hle

set_option maxHeartbeats 1000000 in
theorem X7M2_main (hp : p < ⊤) (eps : ℝ) (heps : 0 < eps) (s : Finset (Lp K p μ)) :
    ∃ P : Lp K p μ →L[K] Lp K p μ, P.comp P = P ∧ ‖P‖ ≤ 1 ∧ FiniteDimensional K P.range ∧
      ∀ x ∈ s, ∃ y ∈ P.range, ‖x - y‖ < eps := by
  classical
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hden := Metric.denseRange_iff.1 (Lp.simpleFunc.denseRange (E := K) (μ := μ) hp.ne)
  have hg : ∀ x : s, ∃ g : Lp.simpleFunc K p μ, dist x.1 (g : Lp K p μ) < eps :=
    fun x => hden x.1 eps heps
  choose g hg using hg
  let φ : s → SimpleFunc A K := fun x => Lp.simpleFunc.toSimpleFunc (g x)
  let G : A → (s → K) := fun a x => φ x a
  have hG : Measurable G := measurable_pi_lambda _ fun x => (φ x).measurable
  have hfin : (Set.range G).Finite := by
    refine (Set.Finite.pi (t := fun x => Set.range (φ x)) fun x => (φ x).finite_range).subset ?_
    rintro _ ⟨a, rfl⟩
    exact fun x _ => ⟨a, rfl⟩
  let T : Set A := G ⁻¹' {0}ᶜ
  have hT : MeasurableSet T := hG (measurableSet_singleton 0).compl
  have hTsub : T ⊆ ⋃ x, Function.support (φ x) := by
    intro a ha
    by_contra hc
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hc
    exact ha (funext hc)
  have hTμ : μ T < ∞ := by
    refine lt_of_le_of_lt (measure_mono hTsub) (lt_of_le_of_lt (measure_iUnion_fintype_le _ _) ?_)
    exact ENNReal.sum_lt_top.2 fun x _ =>
      SimpleFunc.measure_support_lt_top_of_memLp (φ x) (Lp.simpleFunc.memLp _)
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)) hp.ne
  haveI : IsFiniteMeasure (μ.restrict T) := isFiniteMeasure_restrict.2 hTμ.ne
  have hm : MeasurableSpace.comap G inferInstance ≤ m0 := hG.comap_le
  refine ⟨X7M2_P (K := K) (p := p) (μ := μ) (MeasurableSpace.comap G inferInstance) T hT,
    X7M2_P_idem _ T hT hm, LinearMap.mkContinuous_norm_le _ zero_le_one _,
    X7M2_P_fd (K := K) (p := p) (μ := μ) G hG hfin T hT hTμ, ?_⟩
  intro x hx
  have hsup : Function.support (φ ⟨x, hx⟩) ⊆ T := fun a ha h0 => ha (congrFun h0 ⟨x, hx⟩)
  have hind : T.indicator (φ ⟨x, hx⟩) = φ ⟨x, hx⟩ := Set.indicator_eq_self.2 hsup
  have hae : ((g ⟨x, hx⟩ : Lp K p μ) : A → K) =ᵐ[μ] T.indicator (φ ⟨x, hx⟩) := by
    rw [hind]; exact (Lp.simpleFunc.toSimpleFunc_eq_toFun _).symm
  refine ⟨(g ⟨x, hx⟩ : Lp K p μ), ⟨(g ⟨x, hx⟩ : Lp K p μ), ?_⟩, ?_⟩
  · apply Lp.ext
    refine EventuallyEq.trans (X7M2_P_fix _ T hT hm _ (φ ⟨x, hx⟩) ?_ ?_ hae) hae.symm
    · exact ((measurable_pi_apply (⟨x, hx⟩ : s)).comp (comap_measurable G)).stronglyMeasurable
    · exact ((Lp.simpleFunc.memLp _).restrict T).integrable hp1
  · rw [← dist_eq_norm]; exact hg ⟨x, hx⟩

end X7M2

end

noncomputable section

set_option synthInstance.maxSize 8192

open Filter Set

open scoped Topology TensorProduct ENNReal

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

open QAlgorithms.Papers.Independent.Renew46.P04 in
theorem solution {K : Type*} [RCLike K] (A : Type*) [MeasurableSpace A] (mu : MeasureTheory.Measure A)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p < ⊤) :
    MetricPi K (MeasureTheory.Lp K p mu) := by
  intro eps heps s _
  exact X7M2.X7M2_main hp eps heps s

end
