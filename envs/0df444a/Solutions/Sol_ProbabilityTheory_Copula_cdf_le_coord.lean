-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_le_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:58.230968+00:00
-- url     : https://prove2.me/submissions/e4e1f808-c54d-4e4d-9e39-99ecc5132de2

module
public import Definitions.Def_LeanPool_Copula_Basic
public import Definitions.Def_LeanPool_Copula_CDF
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (u : Fin d → I) (i : Fin d) :
    C.cdf u ≤ (u i : ℝ) := by
  calc
    C.cdf u ≤ C.toMeasure.real {x | x i ≤ u i} :=
      measureReal_mono (fun _ hx => hx i)
    _ = (u i : ℝ) := C.measureReal_eval_le i (u i)
end ProbabilityTheory.Copula
