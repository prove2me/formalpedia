-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_cocycle_8537d20491da
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:29.958611+00:00
-- url     : https://prove2.me/submissions/dc38e8d5-d11e-4b71-bac3-877c7dd295fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_a_d_ca60db49e2cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_c_d_ad3e77ed426f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_a_injective_c939b1bb02d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_c_injective_3c88a6526558
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_hh_f82467743477
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_ha0_aefa022df884
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_vc0_4035bdd75d01

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type} [CommRing R]
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
theorem _root_.solution : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x y, Rel n X x y → X.dA n x = 0 ∧ X.dC n y = 0 := by
  intro n
  induction n with
  | zero =>
    intro X hX x y hr
    have hr' := rel_zero.mp hr
    refine ⟨hX.a_injective 1 ?_, hX.c_injective 1 ?_⟩
    · rw [hX.a_d, hr', hX.vc0, map_zero]
    · rw [hX.c_d, ← hr', hX.ha0, map_zero]
  | succ n ih =>
    intro X hX x y hr
    obtain ⟨z, hz, hr⟩ := rel_succ.mp hr
    refine ⟨(ih X.shift hX.shift x (X.up n z) hr).1, hX.c_injective (n + 2) ?_⟩
    rw [hX.c_d, ← hz, hX.hh, map_zero]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
