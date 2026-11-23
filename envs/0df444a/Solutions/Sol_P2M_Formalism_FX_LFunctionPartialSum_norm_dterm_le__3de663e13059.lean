-- Prove2me | solution 1 for P2M_Formalism_FX_LFunctionPartialSum_norm_dterm_le__3de663e13059
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:43.244031+00:00
-- url     : https://prove2.me/submissions/b1a24a02-d8f5-4b87-b193-ad5d6c711982

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LFunctionEqGOfOneLt
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_norm_cpow_sub_le
import Theorems.Thm_Formalism_FX_LFunctionPartialSum_natCast_add_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.FX
open Formalism.FX.LFunctionPartialSum
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.FX.LFunctionPartialSum
theorem _root_.solution {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖dterm χ s n‖ ≤ B * (‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re))) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have key := norm_cpow_sub_le hx hs
  rw [← natCast_add_one_eq, Complex.ofReal_natCast] at key
  show ‖Ap χ n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (hB n) key (norm_nonneg _) hB0
end Formalism.FX.LFunctionPartialSum
