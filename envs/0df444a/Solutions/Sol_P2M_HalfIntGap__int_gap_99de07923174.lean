-- Prove2me | solution 1 for P2M_HalfIntGap__int_gap_99de07923174
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:01.426862+00:00
-- url     : https://prove2.me/submissions/f1d37e8c-e4c1-42a4-8700-9b09025c9420

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HalfIntegerGap_IntGap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HalfIntGap₂
namespace HalfIntGap₂
theorem _root_.solution {N : ℕ} (m : Fin N → ℤ) (hm : StrictAnti m) :
    ∀ d : ℕ, ∀ a b : Fin N, b.val = a.val + d → (d : ℤ) ≤ m a - m b := by
  intro d
  induction d with
  | zero =>
    intro a b h
    have : a = b := Fin.ext (by omega)
    subst this
    simp
  | succ d ih =>
    intro a b h
    have hb' : a.val + d < N := by have := b.isLt; omega
    have h1 := ih a ⟨a.val + d, hb'⟩ rfl
    have hlt : (⟨a.val + d, hb'⟩ : Fin N) < b := by
      rw [Fin.lt_def]; simp; omega
    have h2 := hm hlt
    push_cast
    omega
end HalfIntGap₂
