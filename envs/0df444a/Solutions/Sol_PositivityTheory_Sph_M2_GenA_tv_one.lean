-- Prove2me | solution 1 for PositivityTheory.Sph.M2.GenA.tv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:08.488807+00:00
-- url     : https://prove2.me/submissions/183dc057-48a5-4398-890e-bbca34d24527

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_DgPerm
import Theorems.Thm_PositivityTheory_Sph_M2_GenA_conj_eq
import Theorems.Thm_PositivityTheory_Sph_M2_GenA_tv_mul
import Theorems.Thm_PositivityTheory_Sph_M2_GenA_dg_tv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph PositivityTheory.Sph.M2 PositivityTheory.Sph.M2.GenA
open Matrix
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace PositivityTheory.Sph.M2.GenA
theorem _root_.solution (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) {w : K} (h0 : w ≠ 0) (h1 : 1 + w ≠ 0) {i j : n} (h : i ≠ j)
    (s : K) : ψ (tv h s) = 1 := by
  have e1 := conj_eq ψ hpos (dg_tv h (Units.mk0 w h0) s)
  have e2 := conj_eq ψ hpos (dg_tv h (Units.mk0 _ h1) s)
  have e3 := congrArg ψ (tv_mul h s (w * s))
  simp only [Units.val_mk0] at e1 e2
  rw [map_mul, ← e1, show s + w * s = (1 + w) * s by ring, ← e2] at e3
  exact mul_left_cancel₀ (hpos _).ne' (e3.trans (mul_one _).symm)
end PositivityTheory.Sph.M2.GenA
