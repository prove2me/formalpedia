-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_986af5068273
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:44:41.964235+00:00
-- url     : https://prove2.me/submissions/9ad1d896-cb27-43df-88e2-9820c077ba6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionChowHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecQOfRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionChowHeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionChowHeight_logMean_C_b565892ccd64
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_chowHt_sub_57687e4dc03a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHeight_9bf18eb67ddd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_std_eq_ofPointMatrix_one_d852079b1f83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHeightConst_8b6933d50429


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt)
open GroundTheory.Heights₂.Heights.SectionChowHeight
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.SectionChowHeight
theorem _root_.solution (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (e : ℕ) {a : ℚ} (ha : a ≠ 0) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) 0 = 0 := by
  have hsub := ChowHeightCycleEq.chowHt_sub (fun _ => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (e + 1))
    (fun _ => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw 1 (e + 1)) (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) 0
  simp only [map_C, logMean_C S hS, logMean_C 1 isUnit_one, sub_self, mul_zero,
    Finset.sum_const_zero, zero_div] at hsub
  have hstd : ∀ (σ : ℚ →+* ℂ) (v : Fin n → ℂ),
      ((ArchData.std ℚ n).normAt σ).norm v = IndefiniteRowSideFullHecke.ArithBezout.formNorm 1 v := fun σ v => by
    simp only [ArchData.std]
    rw [ObjectsHeight.std_eq_ofPointMatrix_one, ObjectsHeight.ofPointMatrix_norm]
  have h1 := ObjectsHeight.chowHt_eq_chowHeight (ArchData.std ℚ n) 1 isUnit_one hstd
    (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) (δ := 0)
  rw [chowHeightConst ℚ n (e + 1) _ a ha] at h1
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight at h1 ⊢
  linarith
end GroundTheory.Heights₂.Heights.SectionChowHeight
