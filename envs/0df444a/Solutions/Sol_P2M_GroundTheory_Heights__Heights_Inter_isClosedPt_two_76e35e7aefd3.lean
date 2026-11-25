-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isClosedPt_two_76e35e7aefd3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:48.876306+00:00
-- url     : https://prove2.me/submissions/a17415c6-8ebc-4ed1-8251-1e3fb74380e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_Xc_fc9bcb75d5ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_redTwo_surjective_df3f27242c65
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ptTwo_eq_comap_680e3cb3445e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_X_nmem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution : IsClosedPt ptTwo := by
  have hprime : ptTwo.IsPrime := by
    rw [ptTwo_eq_comap]
    exact Ideal.comap_isPrime _ _
  refine ⟨⟨hprime, ⟨{C 2, Xc 2 1}, ?_, rfl⟩, fun _ => ⟨0, ?_⟩⟩, ?_⟩
  · rintro f (rfl | rfl)
    · refine ⟨fun _ => 0, fun m hm k => ?_⟩
      rw [mem_support_iff, coeff_C] at hm
      split_ifs at hm with h
      · subst h
        simp
      · exact absurd rfl hm
    · exact ⟨_, isMultiHomog_Xc 2 1⟩
  · rw [ptTwo_eq_comap, Ideal.mem_comap]
    have : redTwo (X ⟨(), 0⟩) = X ⟨(), 0⟩ := map_X _ _
    rw [this]
    exact inhV_X_nmem (ZMod 2) _ (by decide)
  · have hsurj : Function.Surjective
        ((Ideal.Quotient.mk (inhV (ZMod 2) ({⟨(), 1⟩} : Finset ((_ : Unit) × Fin 2)))).comp redTwo) :=
      Ideal.Quotient.mk_surjective.comp redTwo_surjective
    have hker : RingHom.ker
        ((Ideal.Quotient.mk (inhV (ZMod 2) ({⟨(), 1⟩} : Finset ((_ : Unit) × Fin 2)))).comp redTwo) =
        ptTwo := by
      rw [ptTwo_eq_comap, ← RingHom.comap_ker, Ideal.mk_ker]
    rw [← hker, ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj), inhV_dim]
    rw [Nat.card_eq_fintype_card, Fintype.card_unit]
    rfl
end GroundTheory.Heights₂.Heights.Inter
