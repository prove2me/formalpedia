-- Prove2me | solution 1 for Section5PowerCode.frame_diagonal_corrected_covariance
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:51:06.27859+00:00
-- url     : https://prove2.me/submissions/c477a726-cee1-41f2-923f-e886031f7ca2

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
import Theorems.Thm_Section5BooleanFrame_tilted_covariance
import Theorems.Thm_Section5PowerCode_codeSign_tilted_polynomial_mean
section
set_option autoImplicit false

namespace Section5PowerCode

variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]







theorem frame_covariance {k : ℕ} (hk : 4 ≤ k) (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v) (w : ι → ℝ) (i j : ι) :
    (∑ t : Fin k → F, frameWeight χ v w t*(codeSign χ v t i*codeSign χ v t j))=
      (if i=j then ∑ l, w l^2 else 0)+2*w i*w j-
        (if i=j then 2*w i^2 else 0) := by
  have hp : (MvPolynomial.X i*MvPolynomial.X j : MvPolynomial ι ℝ).totalDegree+2 ≤ k := by
    have hd := MvPolynomial.totalDegree_mul (MvPolynomial.X i : MvPolynomial ι ℝ)
      (MvPolynomial.X j)
    simp only [MvPolynomial.totalDegree_X] at hd
    omega
  have he := codeSign_tilted_polynomial_mean χ hχ v hv w
    (MvPolynomial.X i*MvPolynomial.X j) hp
  simp only [map_mul,MvPolynomial.eval_X] at he
  change Section5SignMoments.mean _=Section5BooleanFrame.average
    (fun x => Section5BooleanFrame.amplitude w x^2*
      (Section5BooleanFrame.sign x i*Section5BooleanFrame.sign x j)) at he
  rw [Section5BooleanFrame.tilted_covariance] at he
  simpa only [frameWeight,Section5SignMoments.mean,Finset.mul_sum,mul_assoc] using he



end Section5PowerCode

end
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]
theorem solution {k : ℕ} (hk : 4 ≤ k)
    (χ : AddChar F ℝ) (hχ : χ ≠ 0) (v : ι → F) (hv : Function.Injective v)
    (w : ι → ℝ) (hw : ∑ l, w l^2=1) (i j : ι) :
    ((∑ t : Fin k → F, Section5PowerCode.frameWeight χ v w t*(Section5PowerCode.codeSign χ v t i*Section5PowerCode.codeSign χ v t j))-
      (if i=j then 1 else 0))/2+(if i=j then w i^2 else 0)=w i*w j := by
  rw [Section5PowerCode.frame_covariance hk χ hχ v hv w i j,hw]
  split <;> ring
