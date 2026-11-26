-- Prove2me | solution 1 for Uniformization.jankov_von_neumann
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:36.607307+00:00
-- url     : https://prove2.me/submissions/cfc500f8-60d2-4af1-9ce0-6f478d9ad370

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_SolutionJvN
import Theorems.Thm_jankov_von_neumann

section
namespace Uniformization
private theorem jvn_uniformization_delegate {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [PolishSpace Y] (P : Set (X × Y))
    (hP : MeasureTheory.AnalyticSet P) (hne : P.Nonempty) :
    ∃ φ : X → Y,
      @Measurable X Y
        (MeasurableSpace.generateFrom {s : Set X | MeasureTheory.AnalyticSet s}) (borel Y) φ ∧
      ∀ x ∈ Prod.fst '' P, (x, φ x) ∈ P :=
  _root_.jankov_von_neumann P hP hne
end Uniformization
end

set_option autoImplicit false
open Uniformization
namespace Uniformization
theorem _root_.solution {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [PolishSpace Y] (P : Set (X × Y))
    (hP : MeasureTheory.AnalyticSet P) (hne : P.Nonempty) :
    ∃ φ : X → Y,
      @Measurable X Y
        (MeasurableSpace.generateFrom {s : Set X | MeasureTheory.AnalyticSet s}) (borel Y) φ ∧
      ∀ x ∈ Prod.fst '' P, (x, φ x) ∈ P :=
  jvn_uniformization_delegate P hP hne
end Uniformization
