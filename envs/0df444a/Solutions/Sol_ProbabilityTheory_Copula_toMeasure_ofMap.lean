-- Prove2me | solution 1 for ProbabilityTheory.Copula.toMeasure_ofMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:03.549641+00:00
-- url     : https://prove2.me/submissions/aae60bf0-36a5-4f17-a543-1d6852577ac9

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Definitions.Def_LeanPool_Copula_Basic

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory
open ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (X : Ω → Fin d → I) (hX : Measurable X)
    (hmarg : ∀ i, μ.toMeasure.map (fun ω => X ω i) = volume) :
    (ofMap μ X hX hmarg).toMeasure = μ.toMeasure.map X := rfl
end ProbabilityTheory.Copula
