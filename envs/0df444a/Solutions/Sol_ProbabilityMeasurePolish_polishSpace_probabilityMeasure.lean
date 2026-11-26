-- Prove2me | solution 1 for ProbabilityMeasurePolish.polishSpace_probabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:06.11474+00:00
-- url     : https://prove2.me/submissions/f33cabca-2e15-4c87-9ace-52f335a023c7

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_SolutionPolish

set_option autoImplicit false
open MeasureTheory
open ProbabilityMeasurePolish
namespace ProbabilityMeasurePolish
theorem _root_.solution {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    PolishSpace (ProbabilityMeasure X) :=
  _root_.ProbabilityMeasure.instPolishSpace (X := X)
end ProbabilityMeasurePolish
