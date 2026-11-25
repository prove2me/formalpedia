-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.uc_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:08:04.296678+00:00
-- url     : https://prove2.me/submissions/d9b23d25-7481-4551-b983-387e34283852

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_isU_uc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_uc_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex NumberField
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {E : Type} [Field E] [NumberField E]
variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}
variable (hI : IsSplit P I)
include hI
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution {y y' : Vsp X.dim} (hy : y ∈ X.L) (hy' : y' ∈ X.L)
    (hne : uc (IR I) y ≠ uc (IR I) y') :
    Real.sqrt (b0 (E := E) P.q P.R0) ≤ dist (uc (IR I) y) (uc (IR I) y') := by
  rw [dist_eq_norm, ← uc_sub]
  have hu := isU_uc (I := I) (y - y')
  have h0 : uc (IR I) (y - y') ≠ 0 := by rw [uc_sub]; exact sub_ne_zero.2 hne
  have := hI.sep _ (X.L.sub_mem hy hy') _ hu h0
  calc Real.sqrt (b0 (E := E) P.q P.R0) ≤ Real.sqrt (‖uc (IR I) (y - y')‖ ^ 2) := Real.sqrt_le_sqrt this
    _ = _ := Real.sqrt_sq (norm_nonneg _)
end ReciprocityTheory.ChartRestriction.G.I2.Col
