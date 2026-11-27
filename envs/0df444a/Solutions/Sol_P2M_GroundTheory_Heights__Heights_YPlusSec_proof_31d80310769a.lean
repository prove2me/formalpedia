-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSec_proof_31d80310769a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:24.20144+00:00
-- url     : https://prove2.me/submissions/4275229a-801c-4e76-aa19-8d0672fc99eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSec_newEmb_injective_b04c3e7a8d69
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_none_d3bb72b9d852
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSec_mapDomain_newEmb_some_d6e9fc69ab69

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open YPlusSec
namespace GroundTheory.Heights₂.Heights
namespace YPlusSec
theorem _root_.solution : YPlusSec.Statement := by
  intro ι _ _ n P D Ω _ y x' τ
  classical
  unfold Geo.secM
  congr 2
  ext s
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range g (newEmb D) (newEmb_injective D) (by
      intro v hv
      rw [Finset.mem_coe, mem_vars_iff_mem_support] at hv
      obtain ⟨m, hm, hv⟩ := hv
      obtain ⟨o, i⟩ := v
      cases o with
      | none => exact ⟨⟨(), i⟩, rfl⟩
      | some k =>
        exfalso
        have h := hg m hm (some k)
        rw [Pi.single_eq_of_ne (Option.some_ne_none k), Finset.sum_eq_zero_iff] at h
        exact (Finsupp.mem_support_iff.mp hv) (h i (Finset.mem_univ _)))
    refine ⟨q, ?_, ?_⟩
    · intro m hm u
      cases u
      have hm' : Finsupp.mapDomain (newEmb D) m ∈ (rename (newEmb D) q).support := by
        rw [support_rename_of_injective (newEmb_injective D)]
        exact Finset.mem_image_of_mem _ hm
      have h := hg _ hm' none
      simp only [mapDomain_newEmb_none, Pi.single_eq_same] at h
      exact h
    · rw [aeval_rename]
      rfl
  · rintro ⟨q, hq, rfl⟩
    refine ⟨rename (newEmb D) q, ?_, ?_⟩
    · intro m hm k
      rw [support_rename_of_injective (newEmb_injective D), Finset.mem_image] at hm
      obtain ⟨m, hm, rfl⟩ := hm
      cases k with
      | none =>
        simp only [mapDomain_newEmb_none, Pi.single_eq_same]
        exact hq m hm ()
      | some k =>
        simp only [mapDomain_newEmb_some, Finset.sum_const_zero]
        rw [Pi.single_eq_of_ne (Option.some_ne_none k)]
    · rw [aeval_rename]
      rfl
end YPlusSec
end GroundTheory.Heights₂.Heights
