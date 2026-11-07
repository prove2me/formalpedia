-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatPair_intCast_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:56.922241+00:00
-- url     : https://prove2.me/submissions/9f1fedcd-92d0-4029-928c-8079e565daec

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Injective (fun a : ℕ × ℕ => ((a.1 : ℤ), (a.2 : ℤ))) := by
  intro a b h
  apply Prod.ext
  · have hf : (a.1 : ℤ)=(b.1 : ℤ) := congrArg Prod.fst h
    exact_mod_cast hf
  · have hf : (a.2 : ℤ)=(b.2 : ℤ) := congrArg Prod.snd h
    exact_mod_cast hf
end QEC.Coding.TannerLiftedProduct
