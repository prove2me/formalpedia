-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_equiv_da141a3f94b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:28:41.906488+00:00
-- url     : https://prove2.me/submissions/96169fb7-09c9-403c-b16f-44bf8cde6403

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedMod_equiv_bab59235570c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_polyGraded_equiv_07714b7c3c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRingI_equiv_6c221ab935ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRing_equiv_3295007ad279
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_dimCl_equiv_c39cbd206b03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lineX_equiv_6acfbe997019
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_bundleA_equiv_9a6f65d8882f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lmul_equiv_a9ac80d74948
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_zero_sub_b7a88b6ce0bd

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
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace lpow
theorem _root_.solution (Q : Kleiman.SubSystem S x Ω) {b : ℕ} (hb : 1 ≤ b) {i : Fin (N + 1)} (h : x i ≠ 0) :
    IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke Q) b i = toIndefiniteRowSideFullHecke (Q.pow b) i := by
  induction b, hb using Nat.le_induction with
  | base =>
    rw [IndefiniteRowSideFullHecke.Kleiman.lpow, pow_one]
    change toIndefiniteRowSideFullHecke Q i = toIndefiniteRowSideFullHecke ((Q.pow 0).twist Q) i
    rw [← lmul.equiv _ _ h, IndefiniteRowSideFullHecke.Kleiman.lmul]
    apply le_antisymm
    · intro q hq
      have h1 : (1 : Ω) ∈ toIndefiniteRowSideFullHecke (Q.pow 0) i := by
        rw [chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem, pow_zero_sub]
        exact one_mem _
      simpa using Submodule.mul_mem_mul h1 hq
    · rw [Submodule.mul_le]
      intro a ha q hq
      rw [chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem, pow_zero_sub] at ha
      rw [chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem] at hq ⊢
      exact Submodule.smul_mem _ (⟨a, ha⟩ : Kleiman.chartRing S x _) hq
  | succ b hb ih =>
    rw [IndefiniteRowSideFullHecke.Kleiman.lpow, pow_succ]
    change IndefiniteRowSideFullHecke.Kleiman.lpow S (toIndefiniteRowSideFullHecke Q) b i * toIndefiniteRowSideFullHecke Q i = toIndefiniteRowSideFullHecke ((Q.pow b).twist Q) i
    rw [ih, ← lmul.equiv _ _ h]
    rfl
end lpow
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
