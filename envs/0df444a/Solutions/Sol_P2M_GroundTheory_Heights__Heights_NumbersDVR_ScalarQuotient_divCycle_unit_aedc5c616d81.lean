-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_divCycle_unit_aedc5c616d81
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:58.763801+00:00
-- url     : https://prove2.me/submissions/d5169817-bb86-4769-b1ab-af0c1920cfa2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [Fintype K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
theorem _root_.solution (P : Ideal (MRing ι O)) (u : Oˣ) : divCycle P (C (u : O)) = 0 := by
  funext W
  unfold divCycle
  rw [dif_neg]
  · rfl
  rintro ⟨h, -⟩
  have hW : W.IsPrime := h.1.1
  have : P ⊔ Ideal.span {(C (u : O) : MRing ι O)} = ⊤ := by
    rw [Ideal.span_singleton_eq_top.mpr (u.isUnit.map C), sup_top_eq]
  exact hW.ne_top (top_le_iff.mp (this ▸ h.1.2))
end GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient
