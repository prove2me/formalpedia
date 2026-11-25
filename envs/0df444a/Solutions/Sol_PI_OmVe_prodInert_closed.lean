-- Prove2me | solution 1 for PI.OmVe.prodInert_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:00:43.013605+00:00
-- url     : https://prove2.me/submissions/02bf040c-97af-4dfe-99b4-30eddeae0370

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_ProdInertClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
namespace PI.OmVe
theorem _root_.solution (x : ℝ) (hx : x ≠ 0) (M : ℕ) : ∀ a, a ≤ M →
    ∏ j : Fin a, (x ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * x ^ (M - j - 1)) =
      x ^ (2 * M * a - a ^ 2) * ∏ j ∈ Finset.Icc (M - a + 1) M, (1 - (-1) ^ j * x ^ (-(j : ℤ))) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), show a + 1 + m - a + 1 = m + 1 + 1 by omega,
      show a + 1 + m - (a + 1) + 1 = m + 1 by omega,
      ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : m + 1 ≤ a + 1 + m), Finset.prod_insert (by simp),
      zpow_neg, zpow_natCast, show a + 1 + m - a = m + 1 by omega,
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show m + 1 - 1 = m by omega]
    have h1 : 2 * (a + 1 + m) * a - a ^ 2 = a ^ 2 + 2 * a + 2 * a * m := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    have h2 : 2 * (a + 1 + m) * (a + 1) - (a + 1) ^ 2 = a ^ 2 + 2 * a + 2 * a * m + (2 * m + 1) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [h1, h2, pow_add]
    have hw : x ^ (m + 1) ≠ 0 := pow_ne_zero _ hx
    field_simp
    ring
end PI.OmVe
