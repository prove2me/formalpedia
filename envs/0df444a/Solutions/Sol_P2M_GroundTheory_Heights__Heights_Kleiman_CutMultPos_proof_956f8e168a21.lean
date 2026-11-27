-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CutMultPos_proof_956f8e168a21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:34.45981+00:00
-- url     : https://prove2.me/submissions/ac4b9a41-22b3-4728-91bd-1bdf0c9e7019

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutMultPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutMultPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
open IsLocalRing
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace CutMultPos
theorem _root_.solution : CutMultPos.Statement := by
  intro S _ _ N J qq h
  have : qq.IsPrime := h.1.1
  let J' : Ideal (Localization.AtPrime qq) :=
    J.localized' (Localization.AtPrime qq) qq.primeCompl
      (Algebra.linearMap (Poly S N) (Localization.AtPrime qq))
  have hJ' : J' = J.map (algebraMap (Poly S N) (Localization.AtPrime qq)) := by
    simp only [J', Submodule.localized'_eq_span, Ideal.map]
    rfl
  have hmin : maximalIdeal (Localization.AtPrime qq) ∈ J'.minimalPrimes := by
    rw [hJ', IsLocalization.minimalPrimes_map qq.primeCompl, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact h
  have hne : J' ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hmin.1.2
  have : Nontrivial (Localization.AtPrime qq ⧸ J') := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsArtinianRing (Localization.AtPrime qq ⧸ J') :=
    quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J' hmin
  have : IsArtinian (Localization.AtPrime qq) (Localization.AtPrime qq ⧸ J') :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J'))
  have : IsNoetherianRing (Localization.AtPrime qq) :=
    IsLocalization.isNoetherianRing qq.primeCompl _ inferInstance
  unfold cutMult
  rw [← (locQuotEquiv qq J).length_eq]
  exact ⟨Module.length_pos, Module.length_ne_top.lt_top⟩
end CutMultPos
end GroundTheory.Heights₂.Heights.Kleiman
