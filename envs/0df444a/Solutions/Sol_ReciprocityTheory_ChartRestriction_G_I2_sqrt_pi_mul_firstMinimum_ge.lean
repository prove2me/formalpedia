-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.sqrt_pi_mul_firstMinimum_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:18.569328+00:00
-- url     : https://prove2.me/submissions/ad3d6104-f814-4f64-8145-d756104fcf93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) (q : ℕ) (R0 : ℝ) (hq : 1 ≤ q) (hne : Nonempty ι)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) :
    R0 ≤ Real.sqrt (q * Real.pi) * Y.la1 := by
  have hs : 0 < Real.sqrt (q * Real.pi) := by
    apply Real.sqrt_pos.mpr; have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    positivity
  have hcard : 0 < 2 * Fintype.card ι := by have := Fintype.card_pos (α := ι); omega
  have hmem : ∃ t, t ∈ {t : ℝ | ∃ x ∈ lat Y.b, x ≠ 0 ∧ t = ‖x‖} := by
    refine ⟨‖Y.b ⟨0, hcard⟩‖, Y.b ⟨0, hcard⟩, Submodule.subset_span ⟨_, rfl⟩, Y.b.ne_zero _, rfl⟩
  rw [← div_le_iff₀' hs]
  unfold GT.la1
  apply le_csInf hmem
  rintro t ⟨x, hx, hx0, rfl⟩
  rw [div_le_iff₀' hs]
  exact hlat x hx hx0
end ReciprocityTheory.ChartRestriction.G.I2
