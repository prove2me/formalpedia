-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_mul_cycle_25bc873a45af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:10.602793+00:00
-- url     : https://prove2.me/submissions/76c5f5a8-61e1-40df-88f5-319ec50b9c70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionChowHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRecQOfRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionChowHeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionChowHeight_chowHeight_C_986af5068273
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_additive_761cb60a5283
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_cycle_of_A_907b1b4eda67
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHeightMul_of_mahlerMul_2921a84f1e1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahlerMul_d866b4823dac


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
theorem _root_.solution (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) {e : ℕ} {ι : Type}
    (Z : ι →₀ ℕ) (g : ι → MvPolynomial (Fin (e + 1) × Fin n) ℚ) (d : ι → ℕ)
    (hg : ∀ i ∈ Z.support, g i ≠ 0) {a : ℚ} (ha : a ≠ 0) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (C a * ∏ i ∈ Z.support, g i ^ Z i) (∑ i ∈ Z.support, Z i * d i) =
      ∑ i ∈ Z.support, (Z i : ℝ) * IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g i) (d i) := by
  have hMul : ChowHeightMul.Statement := chowHeightMul_of_mahlerMul mahlerMul
  have hne : ∏ i ∈ Z.support, g i ^ Z i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hg i hi)
  have hadd := ChowHeightCycleEq.additive hMul (fun _ : InfinitePlace ℚ => S) (fun _ => hS)
    (C a) (∏ i ∈ Z.support, g i ^ Z i) 0 (∑ i ∈ Z.support, Z i * d i) (C_ne_zero.mpr ha) hne
  have hcyc := ChowHeightCycleEq.cycle_of_A hMul ℚ n e (fun _ => S) (fun _ => hS) ι Z g d hg
  rw [zero_add] at hadd
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight
  rw [hadd]
  have h0 := chowHeight_C S hS e ha
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight at h0
  rw [h0, zero_add]
  exact hcyc
end GroundTheory.Heights₂.Heights.SectionChowHeight
