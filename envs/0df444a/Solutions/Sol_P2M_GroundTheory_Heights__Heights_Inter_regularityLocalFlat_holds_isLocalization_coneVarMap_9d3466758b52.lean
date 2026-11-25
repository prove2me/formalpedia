-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isLocalization_coneVarMap_9d3466758b52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:07:35.202314+00:00
-- url     : https://prove2.me/submissions/f8fe039a-445a-4463-8506-86fd7c6f61a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coneVarMap_injective_1184a2b5fdda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isUnit_coneVarMap_a467678d4c4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_lift_cf8724f91cea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_isUnit_coeff_4e53ac3b7cbc

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
variable {P W}
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution (hPW : P ≤ W) (hPh : IsMultiHomogIdeal P) (hWh : IsMultiHomogIdeal W)
    (v : ∀ k, ι k) (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) :
    haveI := isLocalRing hPW
    letI := (coneVarMap P W hPW v).toRingHom.toAlgebra
    haveI := isPrime_map_C K (maximalIdeal (locRing P W))
    IsLocalization ((maximalIdeal (locRing P W)).map
      (C : locRing P W →+* MvPolynomial K (locRing P W))).primeCompl (coneLocRing P W hPW) := by
  have := isLocalRing hPW
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C K (maximalIdeal (locRing P W))
  rw [isLocalization_iff]
  refine ⟨fun G => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · obtain ⟨G, hG⟩ := G
    have : ∃ e, IsUnit (coeff e G) := by
      by_contra h
      push Not at h
      exact hG (mem_map_C_iff.mpr fun e => (IsLocalRing.mem_maximalIdeal _).mpr (h e))
    obtain ⟨e, he⟩ := this
    exact isUnit_coneVarMap hPW hWh hv G he
  · obtain ⟨⟨x, s⟩, hz⟩ := IsLocalization.surj (W.primeCompl.map (Ideal.Quotient.mk P)) z
    obtain ⟨g, hg, hgs⟩ := s.2
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨F, hF⟩ := exists_lift hPW hv f
    obtain ⟨G, hG⟩ := exists_lift hPW hv g
    have hGq : G ∈ ((maximalIdeal (locRing P W)).map C).primeCompl := by
      intro hmem
      obtain ⟨e, he⟩ := exists_isUnit_coeff hPW G hg hG
      exact (IsLocalRing.mem_maximalIdeal _).mp (mem_map_C_iff.mp hmem e) he
    refine ⟨⟨F, ⟨G, hGq⟩⟩, ?_⟩
    change z * coneVarMap P W hPW v G = coneVarMap P W hPW v F
    rw [hF, hG, hgs]
    exact hz
  · exact ⟨1, by rw [coneVarMap_injective hPW hPh hv hxy]⟩
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
