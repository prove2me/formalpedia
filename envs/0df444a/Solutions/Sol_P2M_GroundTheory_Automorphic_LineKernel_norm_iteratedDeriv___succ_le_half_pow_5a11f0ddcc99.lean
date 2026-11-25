-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_half_pow_5a11f0ddcc99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:10.756147+00:00
-- url     : https://prove2.me/submissions/62958cf9-5fe0-4f04-9a96-488061abd50b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_weight_le_one
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_le_weight
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv_rem_le
import Theorems.Thm_P2M_GroundTheory_Automorphic_LineKernel_norm_iteratedDeriv___succ_le_2cc7e01f7f65


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
variable {M : ℕ → ℝ} {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (hg : ∀ j, Good M ε j (a j))
include hε hg
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (n k : ℕ) (hk : k ≤ n + 1) (t : ℝ) :
    ‖iteratedDeriv k (ρ a (radii ε) (n + 1)) t‖ ≤ (1 / 2) ^ (n + 1) := by
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hS := fun q => norm_iteratedDeriv_rem_le (hr (n + 1)) q
  choose S hS0 hS using hS
  set δ : ℝ := (1 / 2) ^ (n + 1) / ((n + 1 : ℕ) + 2 : ℝ) with hδ
  set B : ℕ → ℝ := fun q => if q < 2 * (n + 1) + 3 then δ else
    2 ^ q * (1 + a (n + 1)) ^ q * exp (-a (n + 1) * radii ε (n + 1)) * S q with hB
  have hBq : ∀ q t, ‖iteratedDeriv q (rem (a (n + 1)) (radii ε (n + 1))) t‖ ≤ B q := by
    intro q t
    simp only [hB]
    split_ifs with hq
    · exact (hg (n + 1)).2.2.1 q (Finset.mem_range.2 hq) t
    · exact hS q (a (n + 1)) (ha _).le t
  refine (norm_iteratedDeriv_ρ_succ_le ha hr n k hBq t).trans ?_
  have h1 : ∀ p ∈ Finset.range (n + 2), coef a (n + 1) p * B (p + k) ≤ δ := by
    intro p hp
    have hp' := Finset.mem_range.1 hp
    have hB' : B (p + k) = δ := by simp only [hB]; rw [if_pos (by omega)]
    rw [hB']
    have hδ0 : 0 ≤ δ := by positivity
    calc coef a (n + 1) p * δ ≤ 1 * δ :=
          mul_le_mul_of_nonneg_right ((coef_le_weight hε hg _ _).trans (weight_le_one M p)) hδ0
      _ = δ := one_mul δ
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hδ]
  have : ((n + 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) + 2 : ℝ) := by push_cast; linarith
  rw [mul_div_assoc']
  rw [div_le_iff₀ (by positivity)]
  have h2 : (0 : ℝ) ≤ (1 / 2) ^ (n + 1) := by positivity
  nlinarith
end GroundTheory.Automorphic.LineKernel
