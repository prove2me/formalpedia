-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_lmul_lpow_e0b30fd3fd3d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:46.533648+00:00
-- url     : https://prove2.me/submissions/eede0b4b-127a-4254-b79e-235ac03129b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_congr_dddc775e54fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_pow_zero_sub_58264d6a7b2c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedMod_equiv_bab59235570c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_PrimeFiltration_equiv_055a468f012b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_bundleA_equiv_9a6f65d8882f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRingI_equiv_6c221ab935ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRing_equiv_3295007ad279
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_dimCl_equiv_c39cbd206b03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lineX_equiv_6acfbe997019
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lmul_equiv_a9ac80d74948
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_equiv_da141a3f94b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_zero_e51216961655
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_polyGraded_equiv_07714b7c3c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (G B : Kleiman.SubSystem S x Ω) (G' B' : Fin (N + 1) → Submodule S Ω)
    (hG : ∀ i, x i ≠ 0 → G' i = toIndefiniteRowSideFullHecke G i) (hB : ∀ i, x i ≠ 0 → B' i = toIndefiniteRowSideFullHecke B i) (b : ℕ) :
    IndefiniteRowSideFullHecke.Kleiman.secs S x (IndefiniteRowSideFullHecke.Kleiman.lmul S G' (IndefiniteRowSideFullHecke.Kleiman.lpow S B' b)) = (G.twist (B.pow b)).secs := by
  rw [← secs.equiv]
  apply secs_congr
  intro i hi
  have e1 : IndefiniteRowSideFullHecke.Kleiman.lmul S G' (IndefiniteRowSideFullHecke.Kleiman.lpow S B' b) i =
      IndefiniteRowSideFullHecke.Kleiman.lmul S (toIndefiniteRowSideFullHecke G) (IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke B) b) i := by
    simp only [IndefiniteRowSideFullHecke.Kleiman.lmul, IndefiniteRowSideFullHecke.Kleiman.lpow, hG i hi, hB i hi]
  rw [e1]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [IndefiniteRowSideFullHecke.Kleiman.lmul, lpow_zero, mul_one, chartModule_of_ne_zero _ hi, chartModule_of_ne_zero _ hi, twist_pow_zero_sub]
  · rw [IndefiniteRowSideFullHecke.Kleiman.lmul, lpow.equiv B hb hi]
    exact lmul.equiv G (B.pow b) hi
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
