-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_toNat_multAt_3727a3dc8d68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:52.873637+00:00
-- url     : https://prove2.me/submissions/09444c52-04cf-4ef9-9a2e-899ee7b9a5bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_localizedQuot_subsingleton_of_not_le_5e934b8b52e3

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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι R)} (f g : MRing ι R)
    {W : Ideal (MRing ι R)} [W.IsPrime] (hW : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes)
    (hrel : IsRelevant W) (hle : P ⊔ Ideal.span {g} ≤ P ⊔ Ideal.span {f}) :
    divCycle P f W = ((multAt (P ⊔ Ideal.span {f}) W).toNat : ℤ) := by
  unfold divCycle
  by_cases hfW : P ⊔ Ideal.span {f} ≤ W
  · have hm : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes :=
      ⟨⟨hW.1.1, hfW⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, hle.trans hQ.2⟩ hQW⟩
    rw [dif_pos ⟨hm, hrel⟩]
  · rw [dif_neg (fun h => hfW h.1.1.2)]
    unfold multAt
    rw [Module.length_eq_zero_iff.mpr (localizedQuot_subsingleton_of_not_le _ W hfW)]
    rfl
end GroundTheory.Heights₂.Heights.NumbersDVR
