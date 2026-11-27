-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KWhit.MeasG.covol_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:04.272715+00:00
-- url     : https://prove2.me/submissions/080754ef-4dc6-4cfd-9fc5-df76635498e7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_WhittakerCovolume_CovolUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.KWhit.MeasG
open MeasureTheory
namespace PositivityTheory.SiegelWeilFormula.KWhit.MeasG
theorem _root_.solution {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    {μ μ' : Measure G} [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure] {𝓕 𝓕' : Set G}
    (h : IsAddFundamentalDomain Γ 𝓕 μ) (h' : IsAddFundamentalDomain Γ 𝓕' μ') (h1 : μ 𝓕 = 1) (h1' : μ' 𝓕' = 1) :
    μ' = μ := by
  have e : μ' = Measure.addHaarScalarFactor μ' μ • μ := Measure.isAddLeftInvariant_eq_smul μ' μ
  have h'' : IsAddFundamentalDomain Γ 𝓕' μ := h'.mono (Measure.absolutelyContinuous_isAddHaarMeasure μ μ')
  have hm : μ 𝓕' = μ 𝓕 := h''.measure_eq h
  have hc : (Measure.addHaarScalarFactor μ' μ : ENNReal) = 1 := by
    have := h1'
    rw [e, Measure.smul_apply, hm, h1, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact this
  have hc' : Measure.addHaarScalarFactor μ' μ = 1 := by exact_mod_cast hc
  rw [e, hc', one_smul]
end PositivityTheory.SiegelWeilFormula.KWhit.MeasG
