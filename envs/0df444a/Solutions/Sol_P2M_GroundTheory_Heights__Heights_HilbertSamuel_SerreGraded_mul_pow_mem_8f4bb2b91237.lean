-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_pow_mem_8f4bb2b91237
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:33.313806+00:00
-- url     : https://prove2.me/submissions/0f642c02-0faa-461f-92f6-9c9d18169fe7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_mul_mem_succ_43982fb32ce9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
theorem _root_.solution (j : Fin q) {k : ℕ} {x : Ω} (hx : x ∈ gradedSpan w d t k) (e : ℕ) :
    x * w j ^ e ∈ gradedSpan w d t (k + e) := by
  induction e with
  | zero => simpa using hx
  | succ e ih =>
    have h := mul_mem_succ w d t j ih
    rw [pow_succ, ← mul_assoc]
    exact h
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
