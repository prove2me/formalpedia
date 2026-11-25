-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_loc_eq_ordLoc_c7fa6570f1d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:13.475732+00:00
-- url     : https://prove2.me/submissions/37f4e55a-a8d6-410b-9d14-9e87dfae5797

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimTwoSumReading
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_map_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_length_localizedModule_quot_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
theorem _root_.solution (W : Ideal A) [hW : W.IsPrime] (a : A) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ Ideal.span {a})) =
      ordLoc ⟨W, hW⟩ a := by
  have h := length_localizedModule_quot_eq (T := Localization.AtPrime W) W.primeCompl ⊥ a
    (fun s hs => IsLocalization.map_units _ (⟨s, hs⟩ : W.primeCompl))
    (fun y => by
      obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj W.primeCompl y
      exact ⟨r, s, s.2, hy.symm⟩)
    (fun r hr => by
      obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff W.primeCompl _ r).mp hr
      exact ⟨s, s.2, (Ideal.mem_bot).mpr hs⟩)
    (fun v hv => by rw [(Ideal.mem_bot).mp hv, map_zero])
  rw [bot_sup_eq] at h
  exact h
end GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
