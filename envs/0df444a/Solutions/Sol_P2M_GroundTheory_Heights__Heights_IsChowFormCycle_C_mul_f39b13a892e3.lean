-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsChowFormCycle_C_mul_f39b13a892e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:30.411166+00:00
-- url     : https://prove2.me/submissions/0d5f0774-8bd8-417d-8c84-bfab6eee9437

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCycleSectionChow

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
namespace GroundTheory.Heights₂.Heights
namespace IsChowFormCycle
theorem _root_.solution {F : Type*} [Field F] {n k : ℕ} {Z : ProjCycle F n}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowFormCycle Z k f) {c : F} (hc : c ≠ 0) :
    IsChowFormCycle Z k (C c * f) := by
  obtain ⟨c', hc', g, hg, rfl⟩ := hf
  exact ⟨c * c', mul_ne_zero hc hc', g, hg, by rw [MvPolynomial.C_mul, mul_assoc]⟩
end IsChowFormCycle
end GroundTheory.Heights₂.Heights
