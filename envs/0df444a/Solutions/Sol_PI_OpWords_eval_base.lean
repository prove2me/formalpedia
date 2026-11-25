-- Prove2me | solution 1 for PI.OpWords.eval_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:52.307343+00:00
-- url     : https://prove2.me/submissions/ea93273d-c7df-4ebc-83e7-abff2726b2a5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishMain
import Theorems.Thm_PI_OpWords_eval_eq_zero_of_support
import Theorems.Thm_PI_OpWords_xdeg_of_bihom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords
theorem _root_.solution {d c : ℕ} (hcd : c < d) (i0 : Fin k) {g : Pol K k} (hg : g ∈ Bihom K k d)
    (hw : WtLe K k c g) (p : Fin k ⊕ Fin k → K) (hx : ∀ b, b ≠ i0 → p (Sum.inl b) = 0)
    (hxi : p (Sum.inr i0) = 0) : eval p g = 0 := by
  apply eval_eq_zero_of_support
  intro m hm
  by_contra hne
  push_neg at hne
  have hzero : ∀ b, b ≠ i0 → m (Sum.inl b) = 0 := by
    intro b hb
    by_contra h0
    exact hne _ h0 (hx b hb)
  have hr : m (Sum.inr i0) = 0 := by
    by_contra h0
    exact hne _ h0 hxi
  have hsum := xdeg_of_bihom hg hm
  rw [Finset.sum_eq_single i0 (fun b _ hb => hzero b hb)
    (fun h => absurd (Finset.mem_univ i0) h)] at hsum
  have h2 := hw m hm i0
  omega
end PI.OpWords
