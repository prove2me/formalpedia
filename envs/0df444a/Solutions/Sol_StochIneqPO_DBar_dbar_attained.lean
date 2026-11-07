-- Prove2me | solution 1 for StochIneqPO.DBar.dbar_attained
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T07:40:29.104285+00:00
-- url     : https://prove2.me/submissions/68fbec3e-b6bb-4fe8-ad90-ae3e24cf2dc8

import Mathlib
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_dbar

open MeasureTheory StochIneqPO.DBar Topology Filter BoundedContinuousFunction

namespace DBarAttAux

abbrev X := (ℤ → ℝ) × (ℤ → ℝ)

lemma continuous_shift' : Continuous (shift (E := ℝ)) :=
  continuous_pi (fun n => continuous_apply _)

lemma continuous_shift2 : Continuous (Prod.map (shift (E := ℝ)) (shift (E := ℝ))) :=
  continuous_shift'.prodMap continuous_shift'

/-- the truncated costs -/
noncomputable def costN (n : ℕ) : X →ᵇ NNReal :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (Real.toNNReal |x.1 0 - x.2 0|) (n : NNReal), by
      refine Continuous.min ?_ continuous_const
      exact continuous_real_toNNReal.comp
        (((continuous_apply 0).comp continuous_fst).sub ((continuous_apply 0).comp continuous_snd)).abs⟩
    n (by
      intro x y
      simp only [ContinuousMap.coe_mk, NNReal.dist_eq]
      have h1 : ((min (Real.toNNReal |x.1 0 - x.2 0|) (n : NNReal) : NNReal) : ℝ) ∈ Set.Icc (0:ℝ) n := by
        constructor
        · positivity
        · exact_mod_cast min_le_right _ _
      have h2 : ((min (Real.toNNReal |y.1 0 - y.2 0|) (n : NNReal) : NNReal) : ℝ) ∈ Set.Icc (0:ℝ) n := by
        constructor
        · positivity
        · exact_mod_cast min_le_right _ _
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])

noncomputable def F (μ : Measure X) : ENNReal := ∫⁻ x, ENNReal.ofReal |x.1 0 - x.2 0| ∂μ

lemma F_eq_iSup (μ : Measure X) : F μ = ⨆ n : ℕ, ∫⁻ x, (costN n x : ENNReal) ∂μ := by
  unfold F
  rw [← lintegral_iSup]
  · congr 1; funext x
    simp only [costN, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk,
      ENNReal.coe_min, ENNReal.coe_natCast]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    rfl
  · intro n
    exact (ENNReal.continuous_coe.comp (costN n).continuous).measurable
  · intro m n hmn x
    simp only [costN, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
    exact_mod_cast min_le_min_left _ (by exact_mod_cast hmn)

lemma F_lsc : LowerSemicontinuous (fun μ : ProbabilityMeasure X => F μ) := by
  have : (fun μ : ProbabilityMeasure X => F μ) =
      fun μ : ProbabilityMeasure X => ⨆ n : ℕ, ∫⁻ x, (costN n x : ENNReal) ∂(μ : Measure X) := by
    funext μ; exact F_eq_iSup μ
  rw [this]
  exact lowerSemicontinuous_iSup (fun n =>
    (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction (costN n)).lowerSemicontinuous)

lemma integrable_cost {μ : Measure X} {P Q : Measure (ℤ → ℝ)}
    (h1 : μ.map Prod.fst = P) (h2 : μ.map Prod.snd = Q)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q) :
    Integrable (fun z : X => |z.1 0 - z.2 0|) μ := by
  have h0 : Measurable (fun ω : ℤ → ℝ => ω 0) := measurable_pi_apply 0
  rw [← h1] at hPi; rw [← h2] at hQi
  have a := (integrable_map_measure h0.aestronglyMeasurable measurable_fst.aemeasurable).mp hPi
  have b := (integrable_map_measure h0.aestronglyMeasurable measurable_snd.aemeasurable).mp hQi
  exact (a.sub b).abs

lemma integral_eq_F (μ : Measure X) :
    ∫ z, |z.1 0 - z.2 0| ∂μ = (F μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z => abs_nonneg _))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  rfl

end DBarAttAux

open DBarAttAux in
theorem solution
    (P Q : Measure (ℤ → ℝ))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q) :
    ∃ ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
      IsPairShiftInvariant ν ∧ ν.map Prod.fst = P ∧ ν.map Prod.snd = Q ∧
      dbar P Q = ∫ z, |z.1 0 - z.2 0| ∂ν := by
  have := hP.1; have := hQ.1
  let P' : ProbabilityMeasure (ℤ → ℝ) := ⟨P, hP.1⟩
  let Q' : ProbabilityMeasure (ℤ → ℝ) := ⟨Q, hQ.1⟩
  let S : Set (ProbabilityMeasure X) :=
    {μ | μ.map continuous_fst.measurable.aemeasurable = P'} ∩
      ({μ | μ.map continuous_snd.measurable.aemeasurable = Q'} ∩
      {μ | μ.map continuous_shift2.measurable.aemeasurable = μ})
  have memS : ∀ ν : Measure X, ∀ hν : IsPairShiftInvariant ν, ν.map Prod.fst = P →
      ν.map Prod.snd = Q → (⟨ν, hν.1⟩ : ProbabilityMeasure X) ∈ S := by
    intro ν hν h1 h2
    refine ⟨?_, ?_, ?_⟩
    · apply ProbabilityMeasure.toMeasure_injective
      exact h1
    · apply ProbabilityMeasure.toMeasure_injective
      exact h2
    · apply ProbabilityMeasure.toMeasure_injective
      exact hν.2
  have ofS : ∀ μ ∈ S, IsPairShiftInvariant (μ : Measure X) ∧
      (μ : Measure X).map Prod.fst = P ∧ (μ : Measure X).map Prod.snd = Q := by
    rintro μ ⟨h1, h2, h3⟩
    refine ⟨⟨inferInstance, ?_⟩, ?_, ?_⟩
    · have := congrArg (fun m : ProbabilityMeasure X => (m : Measure X)) h3
      exact this
    · have := congrArg (fun m : ProbabilityMeasure (ℤ → ℝ) => (m : Measure (ℤ → ℝ))) h1
      exact this
    · have := congrArg (fun m : ProbabilityMeasure (ℤ → ℝ) => (m : Measure (ℤ → ℝ))) h2
      exact this
  have hS_closed : IsClosed S :=
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
      ((isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const).inter
      (isClosed_eq (ProbabilityMeasure.continuous_map continuous_shift2) continuous_id))
  have hT : IsTightMeasureSet {x | ∃ μ ∈ S, (μ : Measure X) = x} := by
    apply IsTightMeasureSet.prodMk
    · apply (isTightMeasureSet_singleton (μ := P)).subset
      rintro _ ⟨_, ⟨μ, hμ, rfl⟩, rfl⟩
      exact (ofS μ hμ).2.1
    · apply (isTightMeasureSet_singleton (μ := Q)).subset
      rintro _ ⟨_, ⟨μ, hμ, rfl⟩, rfl⟩
      exact (ofS μ hμ).2.2
  have hK : IsCompact S :=
    (isCompact_closure_of_isTightMeasureSet hT).of_isClosed_subset hS_closed subset_closure
  -- the product coupling
  have hsh := continuous_shift'.measurable
  have hprod : IsPairShiftInvariant (P.prod Q) :=
    ⟨inferInstance, by rw [← Measure.map_prod_map P Q hsh hsh, hP.2, hQ.2]⟩
  have hne : S.Nonempty := ⟨_, memS (P.prod Q) hprod (by simp) (by simp)⟩
  obtain ⟨μs, hμsS, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK (F_lsc.lowerSemicontinuousOn S)
  obtain ⟨hν, h1, h2⟩ := ofS μs hμsS
  refine ⟨μs, hν, h1, h2, ?_⟩
  unfold dbar
  refine IsLeast.csInf_eq ⟨⟨μs, hν, h1, h2, rfl⟩, ?_⟩
  rintro c ⟨ν', hν', h1', h2', rfl⟩
  rw [integral_eq_F, integral_eq_F]
  have hfin : F ν' ≠ ⊤ := (integrable_cost h1' h2' hPi hQi).lintegral_lt_top.ne
  exact ENNReal.toReal_mono hfin (isMinOn_iff.mp hmin _ (memS ν' hν' h1' h2'))
