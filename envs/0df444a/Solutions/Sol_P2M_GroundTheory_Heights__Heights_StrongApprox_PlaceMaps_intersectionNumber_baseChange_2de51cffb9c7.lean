-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_intersectionNumber_baseChange_2de51cffb9c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:45.928237+00:00
-- url     : https://prove2.me/submissions/7fa468c0-f740-4792-939e-4bbc31b1d1e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_singleV_self_d2ccedef04de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_singleV_ne_7a445a49239f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_e8b57ba56986
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_ne_e03a67a0374a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_inclV_1e030e3a01ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_sigA_singleV_eb561977bf38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_sigA_47589663127e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_inclA_b8a4d4babfbf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_compAt_separates_7b711f540c86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_matrix_separates_f668a50fa67f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_embed_map_self_d8bc151b742b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_embed_map_ne_2cc917f93ef6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_inclA_map_compAt_20da9d9df5df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_form_map_compAt_748dc0e274ac
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution : PlaceMaps.Statement := by
  intro F E _ _ _ _ _ c _ _
  refine ⟨compAt_separates, fun v => ⟨compAt_singleV_self v, fun w h => compAt_singleV_ne h,
    singleV_mul v, fun w h => singleV_mul_ne h, singleV_mul_inclV v, sigA_singleV c v,
    compAt_sigA c v, compAt_inclA v, fun N => ⟨?_, ?_, fun J => ⟨?_, ?_⟩⟩⟩⟩
  · apply matrix_separates; intro w
    by_cases hw : w = v
    · subst hw; rw [embed_map_self]; simp
    · rw [embed_map_ne hw]; simp
  · intro g h
    apply matrix_separates; intro w
    rw [Matrix.map_mul]
    by_cases hw : w = v
    · subst hw; rw [embed_map_self, embed_map_self, embed_map_self]
    · rw [embed_map_ne hw, embed_map_ne hw, embed_map_ne hw, mul_one]
  · rintro g ⟨hdet, hJ⟩
    refine ⟨?_, ?_⟩
    · apply compAt_separates; intro w
      rw [RingHom.map_det, RingHom.mapMatrix_apply, map_one]
      by_cases hw : w = v
      · subst hw; rw [embed_map_self, hdet]
      · rw [embed_map_ne hw, det_one]
    · apply matrix_separates; intro w
      rw [form_map_compAt, inclA_map_compAt]
      by_cases hw : w = v
      · subst hw; rw [embed_map_self]; exact hJ
      · rw [embed_map_ne hw]; simp
  · rintro x ⟨hdet, hJ⟩
    refine ⟨?_, ?_⟩
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
    · have : (xᵀ * J.map (inclA F E) * x.map (sigA c)).map (compAt E v) =
          (J.map (inclA F E)).map (compAt E v) := by rw [hJ]
      rw [form_map_compAt, inclA_map_compAt] at this
      exact this
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
