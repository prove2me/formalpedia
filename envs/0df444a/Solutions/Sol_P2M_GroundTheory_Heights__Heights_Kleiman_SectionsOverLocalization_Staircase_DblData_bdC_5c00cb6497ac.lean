-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_bdC_5c00cb6497ac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:30.912123+00:00
-- url     : https://prove2.me/submissions/39058404-7049-4fd3-b70f-94999a5afe41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_c_d_ad3e77ed426f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_Staircase_DblData_Good_c_injective_3c88a6526558
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
theorem _root_.solution (n : ℕ) (X : DblData R) (hX : X.Good) (y₀ : X.C n) : Rel (n + 1) X 0 (X.dC n y₀) := by
  refine rel_succ.mpr ⟨X.c n y₀, (hX.c_d n y₀).symm, ?_⟩
  have hu : X.up n (X.c n y₀) = 0 := by
    apply hX.shift.c_injective n
    rw [map_zero]
    exact hX.vc0 n y₀
  rw [hu]
  exact Rel.zero n X.shift
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.DblData
