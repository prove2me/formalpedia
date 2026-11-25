-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DehomogOrd_ord_atPrime_ringEquiv_611c8cf7273b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:26:59.602238+00:00
-- url     : https://prove2.me/submissions/b9d1fb24-5b86-4964-afe7-dad0c144201f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ord_ringEquiv_ad3b8618db20


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.DehomogOrd
namespace GroundTheory.Heights₂.Heights.DehomogOrd
theorem _root_.solution {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) (P : Ideal S)
    (P' : Ideal T) [P.IsPrime] [P'.IsPrime] (h : ∀ y, y ∈ P' ↔ e.symm y ∈ P) (x : S) :
    Ring.ord (Localization.AtPrime P') (algebraMap T _ (e x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap S _ x) := by
  have H : P.primeCompl.map e.toMonoidHom = P'.primeCompl := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change e z ∉ P'
      rw [h]
      simpa using hz
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      change e.symm y ∉ P
      rw [← h]
      exact hy
  let f := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime P') e H
  have hf : f (algebraMap S _ x) = algebraMap T _ (e x) :=
    IsLocalization.ringEquivOfRingEquiv_eq (S := Localization.AtPrime P) (Q := Localization.AtPrime P') H x
  rw [← hf]
  exact ord_ringEquiv f _
end GroundTheory.Heights₂.Heights.DehomogOrd
