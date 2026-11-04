-- Prove2me | solution 1 for ThreeSumApsp.IsPowLittleO.eventually_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:51.752292+00:00
-- url     : https://prove2.me/submissions/fd6b9c88-f351-4dcb-bef5-f7d26c2cb191

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
import Theorems.Thm_ThreeSumApsp_Dominated_trans


set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
namespace ThreeSumApsp
namespace IsPowLittleO
theorem _root_.solution (h : IsPowLittleO f a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (n : ℝ) ^ b := by
  obtain ⟨ε, hε, hf⟩ := h
  filter_upwards [hf, hε.eventually_lt_const (sub_pos.2 hab), eventually_ge_atTop 1]
    with n hfn hεn hn
  exact hfn.trans (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hn) (by linarith))
end IsPowLittleO
end ThreeSumApsp
