-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_pos_of_mem_divSupp_5458a53f671d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:06.839806+00:00
-- url     : https://prove2.me/submissions/6261ee01-4c58-437d-9633-ae28196385cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtPosOfMemDivSupp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_length_quot_ne_top_of_mem_minimalPrimes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_length_locQuot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp P s) : 0 < multAt (P ⊔ Ideal.span {s}) W := by
  have hmin := hW.1
  have hWp : W.IsPrime := hmin.1.1
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      ((P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W)]
    rw [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hmin
  have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
  have : Nontrivial (Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
  have hpos := Module.length_pos (R := Localization.AtPrime W)
    (M := Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W)))
  rw [multAt, dif_pos hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
  exact ENat.toNat_pos hpos.ne' hne
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
