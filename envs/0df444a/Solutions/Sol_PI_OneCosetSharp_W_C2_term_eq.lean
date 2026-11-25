-- Prove2me | solution 1 for PI.OneCosetSharp.W.C2.term_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:02.984107+00:00
-- url     : https://prove2.me/submissions/c5293460-70ab-4dfe-921d-a522c8333d35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
import Theorems.Thm_PI_OneCosetSharp_W_C2_sum_eq_chArg
import Theorems.Thm_PI_OneCosetSharp_W_C2_prod_blocks
import Theorems.Thm_PI_OneCosetSharp_W_C2_top_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
open Classical
namespace PI.OneCosetSharp.W.C2
theorem _root_.solution {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ)
    (τ : FC n' (c + 1) n c → k) :
    PhiS ψ₀ χ k₀ m t j n' c n (xx1 (xj0 k₀ n' n) τ) *
        ψ₀ (-chArg (n' := n') (c' := c + 1) (n := n) (c := c) (xx1 (xj0 k₀ n' n) τ)) =
      if ((∀ p', p' < k₀ + m - 1 → ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p' p' = 1) ∧
        (∀ p p', p < n + c → p' < k₀ + m - 1 + (j - 1) * t → p ≠ p' →
          ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' ≠ 0 → Allow k₀ m t (k₀ + m - 1 + (j - 1) * t) p p'))
      then 1 else 0 := by
  unfold PI.OneCosetSharp.PhiS
  dsimp only
  split_ifs with h
  · rw [prod_blocks hN χ τ, top_block hN χ τ h, sum_eq_chArg hN τ]
    rw [inv_one, mul_one, mul_one, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  · rw [zero_mul]
end PI.OneCosetSharp.W.C2
