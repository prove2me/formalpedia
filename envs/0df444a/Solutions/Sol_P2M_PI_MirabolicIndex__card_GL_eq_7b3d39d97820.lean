-- Prove2me | solution 1 for P2M_PI_MirabolicIndex__card_GL_eq_7b3d39d97820
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:40.299769+00:00
-- url     : https://prove2.me/submissions/8b05ea08-3253-4aef-8eb2-96931b9486ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab
import Theorems.Thm_P2M_PI_MirabolicIndex__card_nonzero_92fe098ea246

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.MirabolicIndex₂
open Finset Matrix PI.MirabIndex
variable {k : Type} [Field k] [Fintype k]
namespace PI.MirabolicIndex₂
theorem _root_.solution (n : ℕ) :
    Nat.card (GL (Fin (n + 1)) k) = (Fintype.card k ^ (n + 1) - 1) *
      Nat.card {h : GL (Fin (n + 1)) k // IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} := by
  classical
  have hfib : ∀ v : {v : Fin (n + 1) → k // v ≠ 0},
      Nat.card {h : GL (Fin (n + 1)) k // rowMap n h = v} =
        Nat.card {h : GL (Fin (n + 1)) k // PI.MirabIndex.IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} :=
    fun v => Nat.card_congr (fiberEquiv n v)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (rowMap (k := k) n)), Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_nonzero]
end PI.MirabolicIndex₂
