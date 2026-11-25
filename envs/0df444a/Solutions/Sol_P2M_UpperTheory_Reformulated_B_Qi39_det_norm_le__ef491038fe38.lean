-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:54.34806+00:00
-- url     : https://prove2.me/submissions/21d1a0a3-6b60-44df-b476-404758955859

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qi39
theorem _root_.solution.{u_1} :
    ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] (A : Matrix n n ℂ) {m : ℝ},
      UpperTheory.Reformulated.B.Qi39.EB A m → ‖A.det‖ ≤ (↑(Fintype.card n).factorial : ℝ) * m ^ Fintype.card n := by
  intro n _ _ A m h
  have hterm : ∀ σ : Equiv.Perm n,
      ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ m ^ Fintype.card n := by
    intro σ
    have hs : ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ = ‖∏ i, A (σ i) i‖ := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
      · rw [h1, one_smul]
      · rw [h1, Units.neg_smul, one_smul, norm_neg]
    rw [hs, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : n, m :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => h (σ i) i)
      _ = m ^ Fintype.card n := by rw [Finset.prod_const, Finset.card_univ]
  rw [Matrix.det_apply]
  calc ‖∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm n, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm n, m ^ Fintype.card n := Finset.sum_le_sum fun σ _ => hterm σ
    _ = (↑(Fintype.card n).factorial : ℝ) * m ^ Fintype.card n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
end UpperTheory.Reformulated.B.Qi39
