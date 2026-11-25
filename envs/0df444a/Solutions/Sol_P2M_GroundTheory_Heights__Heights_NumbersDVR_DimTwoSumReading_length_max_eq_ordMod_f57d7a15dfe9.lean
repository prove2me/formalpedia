-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_max_eq_ordMod_f57d7a15dfe9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:16.476507+00:00
-- url     : https://prove2.me/submissions/b0b92806-ad37-494a-af2d-39b1d230219d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimTwoSumReading
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
theorem _root_.solution [IsLocalRing A] (W : Ideal A) [hW : W.IsPrime] (b : A) :
    Module.length (Localization.AtPrime (maximalIdeal A))
        (LocalizedModule (maximalIdeal A).primeCompl (A ⧸ (W ⊔ Ideal.span {b}))) =
      ordMod ⟨W, hW⟩ b := by
  have h := length_localizedModule_quot_eq (T := A ⧸ W) (maximalIdeal A).primeCompl W b
    (fun s hs => (notMem_maximalIdeal.mp hs).map _)
    (fun y => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨r, 1, (maximalIdeal A).primeCompl.one_mem, by simp⟩)
    (fun r hr => ⟨1, (maximalIdeal A).primeCompl.one_mem, by
      rw [one_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mp hr⟩)
    (fun v hv => Ideal.Quotient.eq_zero_iff_mem.mpr hv)
  rw [h, ordMod, Ring.ord, Ideal.Quotient.algebraMap_eq]
end GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
