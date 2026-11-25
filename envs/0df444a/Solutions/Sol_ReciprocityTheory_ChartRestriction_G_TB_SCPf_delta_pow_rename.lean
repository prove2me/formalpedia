-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.delta_pow_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:55:21.54089+00:00
-- url     : https://prove2.me/submissions/48adcba4-d372-4f96-b51e-b68c2e986b5f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_delta_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → s l = true ∧ s l' = false) (n : ℕ) (P : MvPolynomial ι k) :
    (PI.WickFormula.delta (kapE s κ) ^ n) (rename (sideE s) P) =
      rename (sideE s) ((secondOrder k κ)^[n] P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, delta_rename s κ hκ, Function.iterate_succ_apply']
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
