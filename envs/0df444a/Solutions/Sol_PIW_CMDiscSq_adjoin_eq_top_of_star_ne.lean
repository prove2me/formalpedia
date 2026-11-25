-- Prove2me | solution 1 for PIW.CMDiscSq.adjoin_eq_top_of_star_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:26:44.52238+00:00
-- url     : https://prove2.me/submissions/8b9dd296-fc30-4950-acd7-0b1ca3e92eea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_RelDiffTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_AdjoinEqTopOfStarNe
import Theorems.Thm_PIW_CMDiscSq_exists_of_star_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open PIW PIW.CMDiscSq
namespace PIW.CMDiscSq
theorem _root_.solution {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {x : E} (hx : star x ≠ x) :
    Algebra.adjoin F {x} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hd : x - star x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hbd : (y - star y) / (x - star x) * (x - star x) = y - star y := div_mul_cancel₀ _ hd
  have hb : star ((y - star y) / (x - star x)) = (y - star y) / (x - star x) := by
    rw [star_div₀, star_sub, star_sub, star_star, star_star, ← neg_sub y, ← neg_sub x,
      neg_div_neg_eq]
  have ha : star (y - (y - star y) / (x - star x) * x) = y - (y - star y) / (x - star x) * x := by
    rw [star_sub, star_mul', hb]
    linear_combination hbd
  obtain ⟨b, hb'⟩ := exists_of_star_eq hR hb
  obtain ⟨a, ha'⟩ := exists_of_star_eq hR ha
  have hy : y = algebraMap F E a + algebraMap F E b * x := by rw [ha', hb']; ring
  rw [hy]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ a)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ b) (Algebra.subset_adjoin rfl))
end PIW.CMDiscSq
