-- Prove2me | solution 1 for ProbabilityTheory.Copula.cdf_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:46:50.531457+00:00
-- url     : https://prove2.me/submissions/ec5a5256-a97a-44ab-87f0-690d74277878

module
public import Definitions.Def_LeanPool_Copula_Basic
public import Definitions.Def_LeanPool_Copula_CDF
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_eq_zero_of_coord_eq_zero

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) [NeZero d] : C.cdf (fun _ => 0) = 0 :=
  C.cdf_eq_zero_of_coord_eq_zero _ ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ rfl
end ProbabilityTheory.Copula
