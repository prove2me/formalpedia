-- Prove2me | solution 1 for Section5PowerCode.frameWeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:27.114156+00:00
-- url     : https://prove2.me/submissions/68587b48-5ac6-468c-b52b-fe20ee7640aa

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
import Theorems.Thm_Section5PowerCode_codeSign_tilted_polynomial_mean
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]
theorem solution {k : ℕ} (hk : 2 ≤ k) (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v) (w : ι → ℝ) :
    (∑ t : Fin k → F, Section5PowerCode.frameWeight χ v w t)=∑ i, w i^2 := by
  have he := Section5PowerCode.codeSign_tilted_polynomial_mean χ hχ v hv w (1 : MvPolynomial ι ℝ)
    (by simpa using hk)
  simp only [map_one,mul_one] at he
  change Section5SignMoments.mean _=Section5BooleanFrame.average
    (fun x => Section5BooleanFrame.amplitude w x^2) at he
  rw [Section5BooleanFrame.amplitude_second] at he
  simpa only [Section5PowerCode.frameWeight,Section5SignMoments.mean,Finset.mul_sum] using he
