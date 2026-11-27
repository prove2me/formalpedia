-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFFibreMult_proof_3a7f3f0609e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:55.437987+00:00
-- url     : https://prove2.me/submissions/20557a70-7245-47d4-981d-a7acbf6730fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_length_quot_map_of_surjective_9b9a1118e43f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_baseSubst_mul_59b175cd85f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_isUnit_baseSubst_rename_67bd4c226138
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_ker_baseSubst_le_237afa69f022
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_fibreIdeal_eq_map_8dd732a4c3c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_comap_fibreOf_and_isPrime_e91ae4bf3f4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_length_localizedModule_quotient_981ab8107018


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open PFFibreMultProof
namespace GroundTheory.Heights₂.Heights.Inter
namespace PFFibreMult
theorem _root_.solution : PFFibreMult.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d e G s W hv hP' hP hW hH hI
  classical
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P' ≤ W := le_sup_left.trans hW.1.1.2
  obtain ⟨hc, hQ⟩ := comap_fibreOf_and_isPrime hv G W hPW hI
  have := hQ
  set φ := baseSubst κ G with hφ
  have hWQ : W = (fibreOf κ G W).comap φ := hc.symm
  let θ := Localization.localRingHom W (fibreOf κ G W) φ hWQ
  have hcomp : θ.comp (algebraMap (MRing ι') (Localization.AtPrime W)) =
      (algebraMap _ (Localization.AtPrime (fibreOf κ G W))).comp φ :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hWQ z
  have hsurj : Function.Surjective θ := by
    intro y
    obtain ⟨⟨g, h⟩, rfl⟩ := IsLocalization.mk'_surjective (fibreOf κ G W).primeCompl y
    obtain ⟨t, f, ht, e⟩ := exists_baseSubst_mul hv G g
    obtain ⟨t', f', ht', e'⟩ := exists_baseSubst_mul hv G (h : MRingOver G.Φ (fibreIdx ι' κ))
    have htW : ∀ t : MRing ι, aeval G.x t ≠ 0 → rename v t ∉ W := by
      intro t ht h
      have h' : t ∈ imageZ v W := h
      rw [hI, ← G.ker_x, RingHom.mem_ker] at h'
      exact ht h'
    have hf' : f' ∉ W := by
      intro hf'
      apply h.2
      have h1 : φ f' ∈ fibreOf κ G W := by rw [← Ideal.mem_comap, hc]; exact hf'
      rwa [← e', Ideal.unit_mul_mem_iff_mem _ (isUnit_baseSubst_rename hv G ht')] at h1
    have hden : rename v t * f' ∈ W.primeCompl := fun hm =>
      (Ideal.IsPrime.mem_or_mem hWp hm).elim (htW t ht) hf'
    refine ⟨IsLocalization.mk' _ (f * rename v t') ⟨rename v t * f', hden⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul]
    rw [← e, ← e']
    ring
  have hker : RingHom.ker θ ≤ (P' ⊔ Ideal.span {s}).map (algebraMap (MRing ι') (Localization.AtPrime W)) := by
    intro z hz
    obtain ⟨⟨a, w⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl z
    rw [RingHom.mem_ker, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨⟨c, hc'⟩, hc0⟩ := hz
    have hcne : c ≠ 0 := fun h0 => hc' (h0 ▸ (fibreOf κ G W).zero_mem)
    have ha : φ a = 0 := (mul_eq_zero.mp hc0).resolve_left hcne
    have haJ : a ∈ P' ⊔ Ideal.span {s} := Ideal.mem_sup_left (ker_baseSubst_le hv G (RingHom.mem_ker.mpr ha))
    change IsLocalization.mk' (Localization.AtPrime W) a w ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ haJ)
  have hJ : (fibreIdeal κ G ⊔ Ideal.span {φ s}).map (algebraMap _ (Localization.AtPrime (fibreOf κ G W))) =
      ((P' ⊔ Ideal.span {s}).map (algebraMap (MRing ι') (Localization.AtPrime W))).map θ := by
    have hJ0 : fibreIdeal κ G ⊔ Ideal.span {φ s} = (P' ⊔ Ideal.span {s}).map φ := by
      rw [fibreIdeal_eq_map hv G, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rw [hJ0, Ideal.map_map, Ideal.map_map, hcomp]
  unfold multAt
  rw [dif_pos hQ, dif_pos hWp, ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
    ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, hJ,
    length_quot_map_of_surjective θ hsurj _ hker]
end PFFibreMult
end GroundTheory.Heights₂.Heights.Inter
