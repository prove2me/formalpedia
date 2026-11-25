-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_eval_antisymDelta_eq_zero_2ab9ab7fe6fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:30:32.419981+00:00
-- url     : https://prove2.me/submissions/2bb94a28-44d3-453e-8e45-1e0c2dba6880

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (T : Type*) [Fintype T] [DecidableEq T] (N : ℕ) {τ : T}
    {a b : Fin N} (hab : a < b) {x : T × Fin N → ℝ} (hx : x ∈ diagHyperplane T N τ a b) :
    eval x (antisymDelta T N) = 0 := by
  have hx' : x (τ, a) = x (τ, b) := hx
  unfold antisymDelta
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ τ)
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_Ioi.2 hab)
  simp [hx']
end GroundTheory.Heights₂.Heights
