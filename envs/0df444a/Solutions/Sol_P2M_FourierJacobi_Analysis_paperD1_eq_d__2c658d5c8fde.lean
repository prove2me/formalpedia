-- Prove2me | solution 1 for P2M_FourierJacobi_Analysis_paperD1_eq_d__2c658d5c8fde
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:23.953682+00:00
-- url     : https://prove2.me/submissions/a2acdf6c-311f-4589-ad38-7875d9e3560e

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
    paperD1 q a b d = d₁ (inverseSqrt q : ℂ) a b d := by
  simp only [paperD1, satakeTuple, d₁, fourFactors,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one]
  ring
end FourierJacobi.Analysis
