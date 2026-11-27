-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerZeroSpec_proof_8f41ac6bb216
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:04:01.224125+00:00
-- url     : https://prove2.me/submissions/2148cd1c-a9a7-4153-94cd-f4ed380c71da

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PMahlerZeroSpec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_specFirst_zero_38a5baebb2b4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open MeasureTheory MvPolynomial
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
namespace GroundTheory.Heights₂.Heights
namespace MahlerZeroSpec
theorem _root_.solution : MahlerZeroSpec.Statement := by
  intro n h f u
  have hS : {v : Fin 0 × Fin n → ℂ | ∀ i : Fin 0, h.norm (fun j => v (i, j)) < 1} = Set.univ := by
    ext v; simp
  unfold mahler sphereMean
  rw [hS]
  simp_rw [eval_specFirst_zero]
  have h1 : (volume : Measure (Fin 0 × Fin n → ℂ)) Set.univ = 1 := by
    rw [volume_pi]; exact Measure.pi_empty_univ _
  exact setAverage_const (by simp [h1]) (by simp [h1]) _
end MahlerZeroSpec
end GroundTheory.Heights₂.Heights
