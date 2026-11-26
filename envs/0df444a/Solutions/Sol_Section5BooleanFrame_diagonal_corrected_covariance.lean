-- Prove2me | solution 1 for Section5BooleanFrame.diagonal_corrected_covariance
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:11:03.736539+00:00
-- url     : https://prove2.me/submissions/35720912-c620-4cc3-8011-b66f1b586f65

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
import Theorems.Thm_Section5BooleanFrame_tilted_covariance
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem solution (w : ι → ℝ) (hw : ∑ k, w k ^ 2=1) (i j : ι) :
    ((∑ x, Section5BooleanFrame.weight w x*(Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j))-(if i=j then 1 else 0))/2+
      (if i=j then w i ^ 2 else 0)=w i*w j := by
  have he := Section5BooleanFrame.tilted_covariance w i j
  change (Fintype.card (ι → Bool) : ℝ)⁻¹ * _ = _ at he
  rw [Finset.mul_sum] at he
  simp only [Section5BooleanFrame.weight,mul_assoc] at *
  rw [he,hw]
  split <;> ring
