-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.coeff_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:27:11.94819+00:00
-- url     : https://prove2.me/submissions/c4e0a8ca-9a9b-406b-b250-3c3fd0550c5e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
theorem _root_.solution (l : List σ) (m : σ →₀ ℕ) : ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPowerSeries σ ℂ,
    coeff m (l.foldr (fun q G => pderiv ℂ q G) F) = c * coeff (m + (l.map fun q => Finsupp.single q 1).sum) F := by
  induction l generalizing m with
  | nil => exact ⟨1, one_ne_zero, fun F => by simp⟩
  | cons q l ih =>
    obtain ⟨c, hc, hF⟩ := ih (m + Finsupp.single q 1)
    refine ⟨c * ((m q : ℂ) + 1), mul_ne_zero hc (Nat.cast_add_one_ne_zero _), fun F => ?_⟩
    simp only [List.foldr_cons]
    rw [MvPowerSeries.coeff_pderiv, hF, List.map_cons, List.sum_cons, add_assoc]
    ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
