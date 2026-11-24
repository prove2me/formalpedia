-- Prove2me | solution 1 for QPK.haar_measure_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:25:27.704908+00:00
-- url     : https://prove2.me/submissions/07299537-7179-45cf-9401-c095bb711491

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Theorems.Thm_QPK_map_val_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal
open QPK
namespace QPK
theorem _root_.solution : HaarUniq := by
  intro G _ _ _ _ _ _ _ _ K hKc hK μ ν hμ hν
  let H : Subgroup G := toSub K hK
  have hHc : IsClosed (H : Set G) := hKc
  haveI : LocallyCompactSpace H := hHc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have hme : MeasurableEmbedding (Subtype.val : H → G) :=
    MeasurableEmbedding.subtype_coe hKc.measurableSet
  let K₀ : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have key : ∀ ρ : Measure G, InvOn ρ K → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ρ = c • (Measure.haarMeasure K₀).map Subtype.val := by
    intro ρ ⟨hσ, h0, hc, hinv⟩
    let ρ' : Measure H := ρ.comap Subtype.val
    have hback : ρ'.map Subtype.val = ρ := by
      rw [hme.map_comap, Subtype.range_coe]
      exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hc)
    haveI : SigmaFinite ρ' :=
      SigmaFinite.of_map ρ' hme.measurable.aemeasurable (by rw [hback]; exact hσ)
    haveI : IsMulLeftInvariant ρ' := by
      refine ⟨fun g => ?_⟩
      calc ρ'.map (g * ·) = ((ρ'.map (g * ·)).map Subtype.val).comap Subtype.val :=
            (hme.comap_map _).symm
        _ = ((ρ'.map Subtype.val).map ((g : G) * ·)).comap Subtype.val := by rw [map_val_mul]
        _ = ρ' := by rw [hback, hinv (g : G) g.2]
    obtain ⟨c, hK0⟩ : ∃ c : ℝ≥0∞, ρ' = c • Measure.haarMeasure K₀ :=
      ⟨_, Measure.haarMeasure_unique ρ' K₀⟩
    have hρ : ρ = c • (Measure.haarMeasure K₀).map Subtype.val := by
      rw [← hback, hK0, Measure.map_smul]
    refine ⟨c, ?_, ?_, hρ⟩
    · intro hz
      apply h0
      rw [hρ, hz, zero_smul]
    · intro htop
      have hne : Measure.haarMeasure K₀ (⋃ n, spanningSets ρ' n) ≠ 0 := by
        rw [iUnion_spanningSets]
        exact (lt_of_lt_of_le zero_lt_one
          ((Measure.haarMeasure_self (K₀ := K₀)).symm.le.trans (measure_mono (Set.subset_univ _)))).ne'
      obtain ⟨n, hn⟩ : ∃ n, Measure.haarMeasure K₀ (spanningSets ρ' n) ≠ 0 := by
        by_contra hall
        push_neg at hall
        exact hne (measure_iUnion_null_iff.2 hall)
      have h2 : ρ' (spanningSets ρ' n) = (c • Measure.haarMeasure K₀) (spanningSets ρ' n) :=
        congrArg (fun m : Measure H => m (spanningSets ρ' n)) hK0
      have h3 := measure_spanningSets_lt_top ρ' n
      rw [h2, Measure.smul_apply, htop, smul_eq_mul, ENNReal.top_mul hn] at h3
      exact lt_irrefl _ h3
  obtain ⟨a, ha0, hat, hμ'⟩ := key μ hμ
  obtain ⟨b, hb0, hbt, hν'⟩ := key ν hν
  refine ⟨a / b, (ENNReal.div_pos ha0 hbt).ne', ENNReal.div_ne_top hat hb0, ?_⟩
  rw [hμ', hν', smul_smul, ENNReal.div_mul_cancel hb0 hbt]
end QPK
