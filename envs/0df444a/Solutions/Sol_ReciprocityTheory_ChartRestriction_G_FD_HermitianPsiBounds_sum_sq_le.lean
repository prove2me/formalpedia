-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.sum_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:55.284957+00:00
-- url     : https://prove2.me/submissions/6447a329-82cc-42a0-ab70-7f28ec90ac72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPsiBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPsiBounds_inv_c_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
open Matrix NumberField Complex QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
theorem _root_.solution (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) (p : Fin r → E) :
    ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 ≤ Qy X y p * Cinv X := by
  have hc : 0 < X.c τ := by
    have h1 : τ.1 X.ξ0 ≠ 0 := (map_ne_zero _).mpr X.ξ0_ne
    have := norm_pos_iff.mpr h1
    unfold Data.c
    linarith
  have key : ∀ s : ℝ, 0 ≤ s → X.c τ * s ≤ Qy X y p → s ≤ Qy X y p * Cinv X := by
    intro s hs h1
    have h2 := inv_c_le X τ
    have hQ : 0 ≤ Qy X y p := le_trans (mul_nonneg hc.le hs) h1
    calc s = (X.c τ * s) * (1 / X.c τ) := by
          rw [mul_comm (X.c τ), mul_assoc, mul_one_div_cancel hc.ne', mul_one]
      _ ≤ Qy X y p * Cinv X := mul_le_mul h1 h2 (by positivity) hQ
  apply key _ (Finset.sum_nonneg fun _ _ => by positivity)
  unfold Qy
  exact Finset.single_le_sum
    (f := fun τ' => X.c τ' * ∑ a, ‖((y τ')⁻¹ *ᵥ Data.emb τ'.1 p) a‖ ^ 2)
    (fun τ' _ => mul_nonneg (by unfold Data.c; positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)) (Finset.mem_univ τ)
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
