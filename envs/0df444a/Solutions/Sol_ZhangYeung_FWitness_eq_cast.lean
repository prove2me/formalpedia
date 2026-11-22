-- Prove2me | solution 1 for ZhangYeung.FWitness_eq_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:54:23.385847+00:00
-- url     : https://prove2.me/submissions/aed6175e-ed25-4421-b073-0d899180fa8e

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4

set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u
namespace ZhangYeung
theorem _root_.solution (S : Finset (Fin 4)) :
    FWitness S = (FWitnessℚ S : ℝ) := rfl
end ZhangYeung
