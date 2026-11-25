-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.tof_fg_div_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:16:02.101112+00:00
-- url     : https://prove2.me/submissions/1c64c155-54cd-4e1a-bb10-506c6c3ed2b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    (M : Submodule ℤ Q) (hM : M.FG)
    (r : ℕ) (hr : 2 ≤ r) (hdiv : ∀ m ∈ M, ∃ m' ∈ M, m = r • m') : M = ⊥ := by
  obtain ⟨a, ha1, ha⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (Ideal.span {(r : ℤ)}) M hM (by
      intro m hm
      obtain ⟨m', hm', rfl⟩ := hdiv m hm
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hm')
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Ideal.mem_span_singleton] at ha1
    have h1 : (r : ℤ) ∣ 1 := by simpa using ha1
    have h2 := Int.eq_one_of_dvd_one (by positivity) h1
    omega
  rw [eq_bot_iff]
  intro m hm
  have h := ha m hm
  rw [← Int.cast_smul_eq_zsmul ℝ] at h
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast ha0)
end ReciprocityTheory.ChartRestriction.G.I2
