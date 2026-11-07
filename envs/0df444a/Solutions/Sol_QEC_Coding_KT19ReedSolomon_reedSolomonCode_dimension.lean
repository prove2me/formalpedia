-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.reedSolomonCode_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:11:04.057926+00:00
-- url     : https://prove2.me/submissions/6e9308af-14ec-4556-adfe-dd50b6d7a37b

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ReedSolomon_FullLength

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution (p l : Nat) [Fact p.Prime]
    (hlp : l ≤ p) : Dimension (reedSolomonCode p l) = l := by
  change Module.finrank (ZMod p) (LinearMap.range (evaluationLinearMap p l)) = l
  rw [LinearMap.finrank_range_of_inj (evaluationLinearMap_injective p l hlp),
    Module.finrank_eq_card_basis (Polynomial.degreeLT.basis (ZMod p) l), Fintype.card_fin]
end QEC.Coding.KT19ReedSolomon
