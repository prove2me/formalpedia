-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_support_cycleSection_iff_139ed4531e1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:56.067675+00:00
-- url     : https://prove2.me/submissions/9d6849ee-f525-44f7-91a0-487381aa13e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSupportCycleSection

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (Z : ProjCycle ℂ n) (u : Fin n → ℂ)
    (W' : Ideal (MvPolynomial (Fin n) ℂ)) :
    W' ∈ (cycleSection Z u).support ↔ ∃ W ∈ Z.support, W' ∈ (divCycle W u).support := by
  simp only [Finsupp.mem_support_iff, cycleSection, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, ne_eq, Finset.sum_eq_zero_iff, not_forall, mul_eq_zero, not_or, exists_prop]
  constructor <;> rintro ⟨W, h⟩ <;> exact ⟨W, by tauto⟩
end GroundTheory.Heights₂.Heights
