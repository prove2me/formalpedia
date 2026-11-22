-- Prove2me | solution 1 for ProbabilityTheory.Copula.measureReal_rectangle_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:52:26.410523+00:00
-- url     : https://prove2.me/submissions/60de6785-bdc7-4985-8207-9bc26cfda32d

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_two
public import Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_cdf

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula 2) (a b : Fin 2 → I) (hab : a ≤ b) :
    C.toMeasure.real (Set.pi univ (fun i => Ioc (a i) (b i))) =
      C.cdf b - C.cdf ![a 0, b 1] - C.cdf ![b 0, a 1] + C.cdf a := by
  rw [← C.rectangleIncrement_cdf a b hab, rectangleIncrement_two]
end ProbabilityTheory.Copula
