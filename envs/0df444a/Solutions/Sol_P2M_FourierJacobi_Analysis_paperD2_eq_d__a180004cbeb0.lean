-- Prove2me | solution 1 for P2M_FourierJacobi_Analysis_paperD2_eq_d__a180004cbeb0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:12.419848+00:00
-- url     : https://prove2.me/submissions/02a95144-17cc-4af3-a543-e93cd0bbbad7

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (a b d : ℂ) :
    paperD2 q a b d = d₂ (inverseSqrt q : ℂ) a b d := by
  simp only [paperD2, satakeTuple, d₂, fourFactors,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one, div_eq_mul_inv]
  ring
end FourierJacobi.Analysis
