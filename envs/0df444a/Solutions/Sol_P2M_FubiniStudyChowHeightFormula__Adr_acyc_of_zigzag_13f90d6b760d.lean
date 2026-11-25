-- Prove2me | solution 1 for P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_zigzag_13f90d6b760d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:59:37.62933+00:00
-- url     : https://prove2.me/submissions/cf2cbc6d-0be9-4846-ba8f-bba595376c59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DividedPowerAlgebras_AcycOfCoprod
import Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_cm_zigzag_e21921fb67fd
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_id
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_class
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_id
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory GlobalTheory.CatCoh
open FubiniStudyChowHeightFormula₂ FubiniStudyChowHeightFormula₂.Adr
universe v u v' u'
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D]
namespace FubiniStudyChowHeightFormula₂.Adr
theorem _root_.solution (d : D) (h : Zigzag (𝟭 D) ((Functor.const D).obj d)) : Acyc R D := by
  refine ⟨⟨d⟩, fun M ↦ ?_⟩
  obtain ⟨h0, h1, h2⟩ := cm_zigzag M h
  refine ⟨fun g hg a b ↦ (h0 g hg a).trans (h0 g hg b).symm, fun c ↦ ?_, fun c ↦ ?_⟩
  · refine ((CoefMap.pullCohomologyOne_id c).symm.trans (h1 c)).trans ?_
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    refine ⟨0, ?_⟩
    rw [map_zero]
    funext T T' φ
    exact (Z1.id f d).symm
  · refine ((CoefMap.pullCohomologyTwo_id c).symm.trans (h2 c)).trans ?_
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    refine ⟨fun _ _ _ ↦ (z.1 d d d (𝟙 d) (𝟙 d) : M), ?_⟩
    funext T T' T'' φ ψ
    exact sub_add_cancel (z.1 d d d (𝟙 d) (𝟙 d) : M) (z.1 d d d (𝟙 d) (𝟙 d) : M)
end FubiniStudyChowHeightFormula₂.Adr
