-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_quotient_iff_of_isRegularLocalRing_3eacb56911f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:49:45.615016+00:00
-- url     : https://prove2.me/submissions/60f01208-2a15-4589-a7a2-d106c107f429

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMProjDimCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMProjDimCriterion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_nat_eq_of_ne_bot_of_le_ee963b0d7e7a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_quotient_mk_mem_maximalIdeal_d58999d4cb17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_maximalIdeal_of_quotient_mk_4d5502ea0542
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_exists_isRegular_ofList_eq_maximalIdeal
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_of_isRegularLocalRing


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
open IsLocalRing CategoryTheory RingTheory.Sequence
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution
    (hlow : AuslanderBuchsbaumDepthLower.Statement.{0}) (hup : AuslanderBuchsbaumProjDimUpper.Statement.{0})
    (hlen : RegularSequenceLengthLeDim.Statement.{0}) (hcm : CMHeightAddDim.Statement.{0})
    {S : Type} [CommRing S] [IsRegularLocalRing S] (J : Ideal S) (hJm : J ≤ maximalIdeal S) :
    IsCohenMacaulayLocalRing (S ⧸ J) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) ℓ ∧ (ℓ : ℕ∞) ≤ J.height := by
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨rs0, hrs0, hofl, hlen0⟩ := GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := S)
  have hrs0m : ∀ r ∈ rs0, r ∈ maximalIdeal S := fun r hr => hofl ▸ Ideal.subset_span hr
  set d := rs0.length with hd_def
  have hcmS : IsCohenMacaulayLocalRing S :=
    { exists_isWeaklyRegular := ⟨rs0, hrs0m, hrs0.toIsWeaklyRegular, hlen0.symm⟩ }
  have hsum := hcm S J hJ
  rw [← hlen0] at hsum
  obtain ⟨e, he⟩ := exists_nat_eq_of_ne_bot_of_le (x := ringKrullDim (S ⧸ J)) (d := d)
    (ringKrullDim_ne_bot) (hlen0 ▸ ringKrullDim_quotient_le J)
  have hht : J.height ≠ ⊤ := by
    intro h
    rw [h, he] at hsum
    have h2 : ((⊤ : ℕ∞) + e : ℕ∞) = d := by exact_mod_cast hsum
    simp at h2
  obtain ⟨h, hh⟩ : ∃ h : ℕ, J.height = h := ⟨J.height.toNat, (ENat.natCast_toNat hht).symm⟩
  have hhe : h + e = d := by
    rw [hh, he] at hsum; exact_mod_cast hsum
  have hserre : HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ J)) d :=
    GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing hlen0.symm (S ⧸ J)
  constructor
  · intro hCM
    obtain ⟨as, has_m, has_reg, has_len⟩ := hCM.exists_isWeaklyRegular
    obtain ⟨ms, hms⟩ : ∃ ms : List S, ms.map (algebraMap S (S ⧸ J)) = as :=
      ⟨as.map fun a => (Ideal.Quotient.mk_surjective a).choose, by
        rw [List.map_map]; conv_rhs => rw [← List.map_id as]
        exact List.map_congr_left fun a _ => (Ideal.Quotient.mk_surjective a).choose_spec⟩
    have hmsreg : IsWeaklyRegular (S ⧸ J) ms := by
      rw [← isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) ms, hms]; exact has_reg
    have hmsm : ∀ r ∈ ms, r ∈ maximalIdeal S := fun r hr =>
      mem_maximalIdeal_of_quotient_mk (has_m _ (hms ▸ List.mem_map_of_mem hr))
    have hmslen : ms.length = e := by
      have : (as.length : WithBot ℕ∞) = e := has_len.symm.trans he
      rw [← hms, List.length_map] at this; exact_mod_cast this
    have hbound : ∀ rs : List S, (∀ r ∈ rs, r ∈ maximalIdeal S) → IsWeaklyRegular S rs → rs.length ≤ d :=
      fun rs hm hr => by have := hlen S rs hm hr; rw [← hlen0] at this; exact_mod_cast this
    refine ⟨d - e, ?_, ?_⟩
    · have := hup S (S ⧸ J) d d ms hserre hbound hmsm hmsreg
      rwa [hmslen] at this
    · rw [hh]; exact_mod_cast (by omega : d - e ≤ h)
  · rintro ⟨ℓ, hpd, hℓ⟩
    obtain ⟨ms, hmsm, hmsreg, hmslen⟩ := hlow S (S ⧸ J) ℓ rs0 hpd hrs0m hrs0.toIsWeaklyRegular
    have hℓh : ℓ ≤ h := by rw [hh] at hℓ; exact_mod_cast hℓ
    have hle : e ≤ ms.length := by rw [hmslen]; omega
    have hreg' : IsWeaklyRegular (S ⧸ J) (ms.take e) := by
      have := hmsreg; rw [← List.take_append_drop e ms] at this
      exact ((isWeaklyRegular_append_iff (S ⧸ J) _ _).mp this).1
    refine { exists_isWeaklyRegular := ⟨(ms.take e).map (algebraMap S (S ⧸ J)), ?_, ?_, ?_⟩ }
    · intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact quotient_mk_mem_maximalIdeal hJm (hmsm r (List.mem_of_mem_take hr))
    · exact (isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) _).mpr hreg'
    · rw [he, List.length_map, List.length_take, min_eq_left hle]
end GroundTheory.Heights₂.Heights
