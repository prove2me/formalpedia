-- Prove2me | solution 2 for RobustPoA.Static.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:48:18.876883+00:00
-- url     : https://prove2.me/submissions/910cc99d-f2d4-4fd3-b607-157fbdb55376

import Mathlib
import Definitions.Def_RobustPoA_Static_Game
import Definitions.Def_RobustPoA_Static_Smoothness
import Definitions.Def_RobustPoA_Static_Distribution
import Theorems.Thm_RobustPoA_Static_chain_16_21

-- carved verbatim out of submission 22f34412-6fc5-4189-9ffd-06444e669a10, lines 42-63

section
open RobustPoA.Static

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ)
    (hC : ∀ s, 0 ≤ cost C s)
    (hsmooth : ∃ lam mu : ℝ, mu < 1 ∧ IsSmooth C lam mu)
    (σ : (∀ i, S i) →₀ ℝ) (hσ : IsCCE C σ) (sstar : ∀ i, S i) :
    expect σ (cost C) ≤ robustPoA C * cost C sstar := by
  classical
  by_cases hc0 : cost C sstar = 0
  · obtain ⟨lam, mu, hmu, hs⟩ := hsmooth
    have hb := RobustPoA.Static.chain_16_21 C lam mu hs hmu σ hσ sstar
    have hb0 : expect σ (cost C) ≤ 0 := by simpa [hc0] using hb
    have he : ((expect σ (cost C) : ℝ) : EReal) ≤ 0 := by exact_mod_cast hb0
    simpa [hc0] using he
  · have hc : 0 < cost C sstar := lt_of_le_of_ne (hC sstar) (Ne.symm hc0)
    have hinf : ((expect σ (cost C) / cost C sstar : ℝ) : EReal) ≤ robustPoA C := by
      apply le_sInf
      rintro r ⟨lam, mu, hmu, hs, rfl⟩
      have hb := RobustPoA.Static.chain_16_21 C lam mu hs hmu σ hσ sstar
      exact_mod_cast ((div_le_iff₀ hc).2 hb)
    have hec : (0 : EReal) ≤ (cost C sstar : ℝ) := by exact_mod_cast hC sstar
    have hmul := mul_le_mul_of_nonneg_right hinf hec
    simpa only [← EReal.coe_mul, div_mul_cancel₀ _ hc0] using hmul

end
