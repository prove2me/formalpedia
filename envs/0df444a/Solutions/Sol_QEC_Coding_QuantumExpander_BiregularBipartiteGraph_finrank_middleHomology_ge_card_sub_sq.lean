-- Prove2me | solution 1 for QEC.Coding.QuantumExpander.BiregularBipartiteGraph.finrank_middleHomology_ge_card_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:42:52.306789+00:00
-- url     : https://prove2.me/submissions/10a2984e-51b5-4397-8102-64adf1dad89e

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_middleHomology_eq_dimension_products
import Theorems.Thm_QEC_Coding_HypergraphProduct_first_dimension_add_rows_eq_cols_add_transpose_dimension


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumExpander
open QEC.Coding.HypergraphProduct
open scoped ENNReal
universe u
open QEC.Coding.QuantumExpander.BiregularBipartiteGraph
variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
namespace QEC.Coding.QuantumExpander.BiregularBipartiteGraph
theorem _root_.solution
    (G : BiregularBipartiteGraph A B)
    (hSize : Fintype.card B ≤ Fintype.card A) :
    (Fintype.card A - Fintype.card B) ^ 2 ≤
      Module.finrank (ZMod 2) (chainComplex G.hypergraphProductData).middleHomology := by
  let k := Dimension (firstCode G.hypergraphProductData)
  let kT := Dimension (firstTransposeCode G.hypergraphProductData)
  have hRelation :=
    first_dimension_add_rows_eq_cols_add_transpose_dimension
      G.hypergraphProductData
  have hRelation' :
      k + Fintype.card B = Fintype.card A + kT := by
    exact hRelation
  have hCardDecomp :
      Fintype.card A =
        (Fintype.card A - Fintype.card B) + Fintype.card B :=
    (Nat.sub_add_cancel hSize).symm
  have hk : Fintype.card A - Fintype.card B ≤ k := by
    omega
  have hSquare :
      (Fintype.card A - Fintype.card B) *
          (Fintype.card A - Fintype.card B) ≤ k * k :=
    Nat.mul_le_mul hk hk
  rw [finrank_middleHomology_eq_dimension_products]
  change (Fintype.card A - Fintype.card B) ^ 2 ≤
    k * k + kT * kT
  rw [pow_two]
  exact hSquare.trans (Nat.le_add_right (k * k) (kT * kT))
end QEC.Coding.QuantumExpander.BiregularBipartiteGraph
