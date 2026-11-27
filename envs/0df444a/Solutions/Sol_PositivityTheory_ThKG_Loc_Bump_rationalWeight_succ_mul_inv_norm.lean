-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.rationalWeight_succ_mul_inv_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:28.995602+00:00
-- url     : https://prove2.me/submissions/2dcfaffb-73cf-4d5e-ac01-00cd68f4a9e1

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_nm_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate
variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (κ : ι → ℕ) (e : ℕ) {x : ι → ℂ} (hx : ∀ w, x w ≠ 0) :
    r0 κ (e + 1) x * ((∏ w, ‖x w‖ ^ 2 : ℝ) : ℂ)⁻¹ = r0 κ e x := by
  have : ((∏ w, ‖x w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hx).ne'
  rw [mul_inv_eq_iff_eq_mul₀ this]
  push_cast
  rw [r0, r0, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => by ring
end PositivityTheory.ThKG.Loc.Bump
