-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.HorizontalSubsystem.horizontalSubsystem_logicalQubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:48:46.195183+00:00
-- url     : https://prove2.me/submissions/b98ba77b-cccc-4ce0-9832-af9b90253a75

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v
namespace QEC.Coding.BalancedProduct.HorizontalSubsystem
theorem _root_.solution
    {G aRow aCol : Type} [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (A : Matrix aRow aCol (MonoidAlgebra (ZMod 2) G)) (x : G)
    (hOdd : Odd (Fintype.card G)) :
    (horizontalSubsystem A x hOdd).logicalQubits =
      Module.finrank (ZMod 2) (quotientTannerComplex A).middleHomology :=
  rfl
end QEC.Coding.BalancedProduct.HorizontalSubsystem
