-- Prove2me | solution 1 for OAI.thetaGammaSeven_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:44:17.386739+00:00
-- url     : https://prove2.me/submissions/68c04c67-2e8a-4a23-afc8-b81f94428bc9

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_mul
import Theorems.Thm_OAI_ActualEisensteinCubic_breveGamma2_cube
import Theorems.Thm_OAI_ShortDraftLatticeCount_qNat_mul


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
namespace OAI
theorem _root_.solution :
    thetaGammaSeven ^ 3 = -eisEmbedding pSeven / (‖eisEmbedding pSeven‖ : ℂ) := by
  unfold thetaGammaSeven
  let : PSeven.IsMaximal := PSeven_maximal
  exact ActualEisensteinCubic.breveGamma2_cube PSeven
    (by
      rw [theta_counter_lambda_eq]
      intro hh
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hh
      have hnorm := congrArg ShortDraftLatticeCount.qNat hx
      rw [ShortDraftLatticeCount.qNat_mul, pSeven_norm, lambda7_norm] at hnorm
      omega)
    pSeven rfl pSeven_ne
    (by
      rw [theta_counter_lambda_eq]
      refine ⟨-1, ?_⟩
      rw [pow_two, ActualEisensteinCoordinates.eval_mul]
      norm_num [pSeven, ActualEisensteinCoordinates.eval])
end OAI
