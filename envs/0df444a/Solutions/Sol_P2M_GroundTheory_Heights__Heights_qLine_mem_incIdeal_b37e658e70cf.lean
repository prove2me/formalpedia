-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_qLine_mem_incIdeal_b37e658e70cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:39:25.258395+00:00
-- url     : https://prove2.me/submissions/7a602cc6-1e37-473c-aaf6-23fa468fd1d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder

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
open MvPolynomial
noncomputable section
open LineChowForm
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : qLine ∈ incIdeal (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}) 1 := by
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  rintro v ⟨x, hx0, hxW, hv⟩
  have h0 : x 0 = 0 := by simpa using hxW (X 0) (Ideal.mem_span_singleton_self _)
  have h1 : x 1 ≠ 0 := fun h1 => hx0 (funext fun j => by fin_cases j <;> simp [h0, h1])
  have h := hv 0
  rw [Fin.sum_univ_two, h0, mul_zero, zero_add] at h
  simp [qLine, (mul_eq_zero.mp h).resolve_right h1]
end GroundTheory.Heights₂.Heights
