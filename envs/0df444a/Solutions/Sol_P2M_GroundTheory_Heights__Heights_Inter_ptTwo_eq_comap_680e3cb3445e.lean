-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ptTwo_eq_comap_680e3cb3445e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:16.185165+00:00
-- url     : https://prove2.me/submissions/a04abdc8-74a1-436f-861a-a2b1c9090eb8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_redTwo_surjective_df3f27242c65
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_singleton


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
theorem _root_.solution :
    ptTwo = (inhV (ZMod 2) ({⟨(), 1⟩} : Finset ((_ : Unit) × Fin 2))).comap redTwo := by
  have h1 : inhV (ZMod 2) ({⟨(), 1⟩} : Finset ((_ : Unit) × Fin 2)) =
      Ideal.map redTwo (Ideal.span {Xc 2 1}) := by
    rw [inhV_singleton, Ideal.map_span, Set.image_singleton]
    simp [Xc]
  rw [h1, Ideal.comap_map_of_surjective _ redTwo_surjective, ← RingHom.ker_eq_comap_bot,
    MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, ptTwo,
    Ideal.span_insert, sup_comm]
  simp
end GroundTheory.Heights₂.Heights.Inter
