-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.exists_FT_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:08.712174+00:00
-- url     : https://prove2.me/submissions/c1a71021-9cf5-4dd7-86f0-1cb03ce5c162

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ContinuousOnRationalWeight
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_RationalWeightSuccMulInvNorm
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_core_bump
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_fourier_vanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap RealInnerProductSpace ComplexConjugate
variable {ι : Type} [Fintype ι] {n : Type} [Fintype n] {K : Type} [TopologicalSpace K]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {a : (ι → ℂ) → ℂ} (ha : Continuous a) (hi : Integrable a) (h0 : a 0 ≠ 0) : ∃ t, FT a t ≠ 0 := by
  by_contra hn
  push Not at hn
  let π : (ι → ℂ) → XS ι := fun x => WithLp.toLp 2 fun w => 2 * x w
  have hπ : Continuous π := by fun_prop
  obtain ⟨φ, -, -, hφ⟩ := core_bump volume π hπ 0 (fun x => a x * (a 0)⁻¹) univ (Metric.closedBall 0 1) isOpen_univ
    (ha.mul continuous_const).continuousOn (isCompact_closedBall _ _) (subset_univ _) 1 one_pos (fun x hx => by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_
      have h1 := (PiLp.norm_apply_le (π x) w).trans ((dist_zero_right _).symm.le.trans hx)
      simp only [π, norm_mul, Complex.norm_ofNat] at h1
      linarith [norm_nonneg (x w)]) (fun x hx => by
      have : x = 0 := funext fun w => by simpa [π] using congrArg (fun y : XS ι => y w) hx
      simp [this, h0]) 0 (by ext w; simp [π])
  refine hφ (fourier_vanish _ π hπ.measurable _ (hi.mul_const _) (fun η => ?_) φ)
  simp only [← mul_assoc]
  rw [integral_mul_const]
  have := hn fun w => -conj (η w)
  rw [FT] at this
  refine mul_eq_zero_of_left (Eq.trans ?_ this) _
  congr 1; funext x; congr 2
  simp only [pr, π, PiLp.inner_apply, Complex.inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp; ring
end PositivityTheory.ThKG.Loc.Bump
