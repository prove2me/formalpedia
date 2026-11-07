-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsLeastPrimeAbove_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:31:07.718727+00:00
-- url     : https://prove2.me/submissions/613d6df5-6bfe-44c7-b522-f91bda6f353d

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {p : ℕ} (hp : p.Prime) (B q : ℕ)
    (hq : lpsPrimeCandidate p B q) : lpsLeastPrimeAbove hp B ≤ q :=
  Nat.find_min' (exists_lpsPrimeCandidate hp B) hq
end QEC.Coding.TannerLiftedProduct
