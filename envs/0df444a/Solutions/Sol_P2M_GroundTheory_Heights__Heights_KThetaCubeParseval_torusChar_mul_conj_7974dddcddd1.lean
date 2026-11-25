-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_torusChar_mul_conj_7974dddcddd1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:01:18.673874+00:00
-- url     : https://prove2.me/submissions/3156ef70-1beb-4397-be2a-219c8fb735d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaCubeParseval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaCubeParseval_torusChar_eq_8a9d063e55cf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Real ComplexConjugate
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaCubeParseval
namespace GroundTheory.Heights₂.Heights.KThetaCubeParseval
theorem _root_.solution {g : ℕ} (k l : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar k u * conj (torusChar l u) = torusChar (k - l) u := by
  rw [torusChar_eq, torusChar_eq, torusChar_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.KThetaCubeParseval
