-- Prove2me | solution 1 for ShortWDRODual.MaxCost.ec1_attained
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:07:04.167241+00:00
-- url     : https://prove2.me/submissions/9f680b8b-1ac1-48be-9311-bc477e12fe4a

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.MaxCost Filter Topology
open scoped ENNReal BoundedContinuousFunction

theorem solution {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat P : Measure X) [IsProbabilityMeasure Phat] [IsProbabilityMeasure P]
    (c : X → X → ℝ) (hc : Continuous (fun q : X × X => c q.1 q.2))
    (hcnn : ∀ x y, 0 ≤ c x y)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hK : maxCost c Phat P ≤ ENNReal.ofReal ρ) :
    ∃ γ ∈ couplings Phat P,
      essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2)) γ ≤ ENNReal.ofReal ρ := by
  -- Step 1: near-optimal couplings `γ n` with `γ n`-ess sup `c < ρ + 1/(n+1)`.
  have hn : ∀ n : ℕ, ∃ γ ∈ couplings Phat P,
      essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2)) γ <
        ENNReal.ofReal (ρ + 1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : maxCost c Phat P < ENNReal.ofReal (ρ + 1 / ((n : ℝ) + 1)) :=
      lt_of_le_of_lt hK ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
    unfold maxCost at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨γ, hγ, h⟩ := hlt
    exact ⟨γ, hγ, h⟩
  choose γ hγ hess using hn
  let μ : ℕ → ProbabilityMeasure (X × X) := fun n => ⟨γ n, (hγ n).1⟩
  have hμ : ∀ n, ((μ n : ProbabilityMeasure (X × X)) : Measure (X × X)) = γ n := fun n => rfl
  -- Step 2: tightness and Prokhorov.
  have htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure (X × X)) : Measure (X × X)) | ν ∈ Set.range μ} := by
    apply IsTightMeasureSet.prodMk
    · apply (isTightMeasureSet_singleton (μ := Phat)).subset
      rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact (hγ n).2.1
    · apply (isTightMeasureSet_singleton (μ := P)).subset
      rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact (hγ n).2.2
  have hcomp := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨ν, -, hν⟩ := hcomp.exists_mapClusterPt (f := atTop) (u := μ)
    (tendsto_principal.2 (Eventually.of_forall fun n => subset_closure ⟨n, rfl⟩))
  rw [mapClusterPt_atTop_iff_forall_mem_closure] at hν
  -- closed conditions pass to the cluster point
  have hpass : ∀ (C : Set (ProbabilityMeasure (X × X))), IsClosed C → ∀ m : ℕ,
      (∀ n, m ≤ n → μ n ∈ C) → ν ∈ C := by
    intro C hC m hm
    refine closure_minimal ?_ hC (hν m)
    rintro _ ⟨n, hn, rfl⟩
    exact hm n hn
  -- Step 3: marginals.
  have hmarg : ∀ (π : X × X → X) (hπ : Continuous π) (Q : Measure X) [IsProbabilityMeasure Q],
      (∀ n, (γ n).map π = Q) → (ν : Measure (X × X)).map π = Q := by
    intro π hπ Q _ hQ
    let Q' : ProbabilityMeasure X := ⟨Q, inferInstance⟩
    have hC : IsClosed {m : ProbabilityMeasure (X × X) |
        m.map hπ.measurable.aemeasurable = Q'} :=
      isClosed_eq (ProbabilityMeasure.continuous_map hπ) continuous_const
    have := hpass _ hC 0 (fun n _ => by
      show ProbabilityMeasure.map (μ n) hπ.measurable.aemeasurable = Q'
      apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map]
      exact hQ n)
    have h2 := congrArg (fun m : ProbabilityMeasure X => (m : Measure X)) this
    simp only [ProbabilityMeasure.toMeasure_map] at h2
    exact h2
  have hν1 := hmarg Prod.fst continuous_fst Phat (fun n => (hγ n).2.1)
  have hν2 := hmarg Prod.snd continuous_snd P (fun n => (hγ n).2.2)
  -- Step 4: the support condition, via `g = min 1 (c - ρ)_+`.
  let g : X × X → ℝ := fun q => min 1 (max (c q.1 q.2 - ρ) 0)
  have hg : Continuous g := continuous_const.min ((hc.sub continuous_const).max continuous_const)
  have hg0 : ∀ q, 0 ≤ g q := fun q => le_min zero_le_one (le_max_right _ _)
  have hg1 : ∀ q, g q ≤ 1 := fun q => min_le_left _ _
  let G : (X × X) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨g, hg⟩ 1 (by
    intro x y
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]
    constructor <;> linarith [hg0 x, hg0 y, hg1 x, hg1 y])
  have hG : ∀ q, G q = g q := fun q => rfl
  have hGn : ∀ n : ℕ, ∫ q, G q ∂(γ n) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have := (hγ n).1
    have hae : ∀ᵐ q ∂(γ n), G q ≤ 1 / ((n : ℝ) + 1) := by
      filter_upwards [ae_lt_of_essSup_lt (hess n)] with q hq
      rw [hG]
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hq' : c q.1 q.2 < ρ + 1 / ((n : ℝ) + 1) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hq
      exact (min_le_right _ _).trans (max_le (by linarith) hpos.le)
    calc ∫ q, G q ∂(γ n) ≤ ∫ _q, 1 / ((n : ℝ) + 1) ∂(γ n) :=
          integral_mono_ae (G.integrable _) (integrable_const _) hae
      _ = 1 / ((n : ℝ) + 1) := by simp
  have hint_le : ∀ m : ℕ, ∫ q, G q ∂(ν : Measure (X × X)) ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    have hC : IsClosed {m' : ProbabilityMeasure (X × X) |
        ∫ q, G q ∂(m' : Measure (X × X)) ≤ 1 / ((m : ℝ) + 1)} :=
      isClosed_le (ProbabilityMeasure.continuous_integral_boundedContinuousFunction G)
        continuous_const
    refine hpass _ hC m (fun n hn => ?_)
    show ∫ q, G q ∂(γ n) ≤ 1 / ((m : ℝ) + 1)
    refine (hGn n).trans ?_
    gcongr
  have hint0 : ∫ q, G q ∂(ν : Measure (X × X)) = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat hint_le
    · exact integral_nonneg fun q => hg0 q
  have hae0 : (fun q => G q) =ᵐ[(ν : Measure (X × X))] 0 :=
    (integral_eq_zero_iff_of_nonneg (f := fun q => G q) (fun q => hg0 q) (G.integrable _)).mp hint0
  refine ⟨(ν : Measure (X × X)), ⟨inferInstance, hν1, hν2⟩, ?_⟩
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [hae0] with q hq
  simp only [Pi.zero_apply, hG] at hq
  apply ENNReal.ofReal_le_ofReal
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  have : 0 < g q := lt_min zero_lt_one (lt_max_of_lt_left (by linarith))
  linarith
