-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IndexUBound.inner_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:41.769624+00:00
-- url     : https://prove2.me/submissions/fc77f64b-6378-4291-b260-5480e01ca274

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexUpperBound_OneSubSumLeProd
import Theorems.Thm_PI_UnitaryGroupMassFormula_IndexUBound_one_sub_sum_le_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IndexUBound
open Finset
namespace PI.UnitaryGroupMassFormula.IndexUBound
theorem _root_.solution (g : ℝ) (hg : 2 ≤ g) (r : ℕ) :
    0 ≤ ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) ∧ ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) ≤ 1 ∧
      1 - 1 / (g - 1) ≤ ∏ i ∈ Ico 1 r, (1 - g⁻¹ ^ i) := by
  have hg0 : 0 < g := by linarith
  set x := g⁻¹ with hx
  have hx0 : 0 < x := inv_pos.2 hg0
  have hx1 : x ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hxg : x * g = 1 := inv_mul_cancel₀ hg0.ne'
  have hpow0 : ∀ i : ℕ, 0 ≤ x ^ i := fun i => pow_nonneg hx0.le i
  have hpow1 : ∀ i : ℕ, x ^ i ≤ 1 := fun i => pow_le_one₀ hx0.le hx1
  have hf0 : ∀ i ∈ Ico 1 r, 0 ≤ 1 - x ^ i := fun i _ => sub_nonneg.2 (hpow1 i)
  have hf1 : ∀ i ∈ Ico 1 r, 1 - x ^ i ≤ 1 := fun i _ => by linarith [hpow0 i]
  refine ⟨Finset.prod_nonneg hf0, Finset.prod_le_one hf0 hf1, ?_⟩
  have hS : (∑ i ∈ Ico 1 r, x ^ i) * (g - 1) ≤ 1 := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · have h := geom_sum_Ico_mul x hr
      have e : (∑ i ∈ Ico 1 r, x ^ i) * (g - 1) = 1 - x ^ r * g := by
        linear_combination (-g) * h + ((∑ i ∈ Ico 1 r, x ^ i) + 1) * hxg
      rw [e]
      nlinarith [hpow0 r]
  have hS' : ∑ i ∈ Ico 1 r, x ^ i ≤ 1 / (g - 1) := by
    rw [le_div_iff₀ (by linarith)]
    exact hS
  have h1 := PI.UnitaryGroupMassFormula.IndexUBound.one_sub_sum_le_prod (Ico 1 r) (fun i => 1 - x ^ i)
    (fun i => x ^ i) hf0 hf1 (fun i _ => hpow0 i) (fun i _ => le_refl _)
  beta_reduce at h1
  linarith
end PI.UnitaryGroupMassFormula.IndexUBound
