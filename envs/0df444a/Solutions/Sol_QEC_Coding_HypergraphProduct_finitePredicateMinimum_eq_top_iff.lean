-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.finitePredicateMinimum_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:43.369204+00:00
-- url     : https://prove2.me/submissions/61430718-d880-47de-9966-0e64db89aedd

import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Theorems.Thm_QEC_Coding_HypergraphProduct_finitePredicateMinimum_le_of
import Theorems.Thm_QEC_Coding_HypergraphProduct_le_finitePredicateMinimum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {P : alpha → Prop} [DecidablePred P] {weight : alpha → Nat} :
    finitePredicateMinimum P weight = ⊤ ↔ ∀ x, ¬ P x := by
  constructor
  · intro htop x hx
    have hle := finitePredicateMinimum_le_of (weight := weight) hx
    rw [htop] at hle
    exact (WithTop.not_top_le_coe (weight x) hle)
  · intro hnone
    apply top_unique
    apply le_finitePredicateMinimum
    intro x hx
    exact (hnone x hx).elim
end QEC.Coding.HypergraphProduct
