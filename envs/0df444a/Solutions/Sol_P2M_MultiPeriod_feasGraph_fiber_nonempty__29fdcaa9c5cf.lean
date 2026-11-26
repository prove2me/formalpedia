-- Prove2me | solution 1 for P2M_MultiPeriod_feasGraph_fiber_nonempty__29fdcaa9c5cf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:42.994884+00:00
-- url     : https://prove2.me/submissions/48a41149-4442-44b2-a938-7b9199e95e94

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MultiPeriod_Feas_nonempty
import Theorems.Thm_MultiPeriod_feasGraph_fiber_nonempty
import Theorems.Thm_P2M_CouplingSet__nonempty_2818265cb747
import Theorems.Thm_P2M_FeasibleSet__nonempty_294b52d3ec45


set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, PolishSpace (Y n)] [∀ n, BorelSpace (Y n)]
namespace MultiPeriod
theorem _root_.solution (t : ℕ) (h : PairHist X Y t) :
    ∃ γ : WeakP (X (t + 1) × Y (t + 1)),
      (h, γ) ∈ FeasGraph (fun t x => (κμP t x : Measure (X (t + 1))))
        (fun t y => (κνP t y : Measure (Y (t + 1)))) t :=
  feasGraph_fiber_nonempty _ _ (fun _ _ => inferInstance)
    (Feas.nonempty _ _ (fun _ _ => inferInstance) (fun _ _ => inferInstance))
    t h
end MultiPeriod
