-- Prove2me | solution 1 for SimpleCorrMFG.Conv.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:43:02.152972+00:00
-- url     : https://prove2.me/submissions/5d9633ce-ad1d-403a-bff9-a9229f9d551f

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_RegCondDistrib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory unitInterval Filter Topology SimpleCorrMFG.Conv

theorem solution {Ω 𝒴 : Type*} (C G C' : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → 𝒴) (κ : Ω → ProbabilityMeasure 𝒴) (hY : Measurable Y) (hκ : Measurable κ)
    (hCG : C ≤ G) (hGC' : G ≤ C') (hC' : C' ≤ mΩ)
    (hC : IsRegCondDistrib P Y (fun ω => (κ ω : Measure 𝒴)) C)
    (hC'rcd : IsRegCondDistrib P Y (fun ω => (κ ω : Measure 𝒴)) C') :
    IsRegCondDistrib P Y (fun ω => (κ ω : Measure 𝒴)) G := by
  refine ⟨hC.1, fun A hA => ?_⟩
  refine ⟨(hC.2 A hA).1.mono hCG le_rfl, fun s hs => ?_⟩
  exact (hC'rcd.2 A hA).2 s (hGC' s hs)
