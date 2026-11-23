-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_card_le_trdeg_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:29.550035+00:00
-- url     : https://prove2.me/submissions/21467eea-ba62-43ad-a49a-4e6d8a79ea39

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {F E C : Type} [Field F] [Field E] [Field C] [Algebra F E] [Algebra E C]
    [Algebra F C] [IsScalarTower F E C] {σ τ : Type} (tb : σ → C) (ub : τ → C)
    (hu : AlgebraicIndependent F ub) (hmem : ∀ j, ub j ∈ Algebra.adjoin E (Set.range tb)) :
    Cardinal.mk τ ≤ Algebra.trdeg F E + Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) := by
  haveI : FaithfulSMul F E :=
    (faithfulSMul_iff_algebraMap_injective F E).mpr (algebraMap F E).injective
  haveI : FaithfulSMul E (Algebra.adjoin E (Set.range tb)) :=
    (faithfulSMul_iff_algebraMap_injective E _).mpr (algebraMap E _).injective
  rw [trdeg_add_eq F E (A := Algebra.adjoin E (Set.range tb))]
  have hu' : AlgebraicIndependent F (fun j => (⟨ub j, hmem j⟩ : Algebra.adjoin E (Set.range tb))) :=
    AlgebraicIndependent.of_comp ((Algebra.adjoin E (Set.range tb)).val.restrictScalars F) hu
  exact hu'.cardinalMk_le_trdeg
end ReciprocityTheory.MultiplicativeHeights
