-- Prove2me | solution 1 for Section5PowerCode.tilted_batch_polynomial_match
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:51:07.825779+00:00
-- url     : https://prove2.me/submissions/4e820ad1-c605-43a9-9dc3-0672cb133a0d

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
import Theorems.Thm_Section5PowerCode_codeSign_tilted_polynomial_mean
import Theorems.Thm_Section5SignMoments_tensor_polynomial_mean_match
section
set_option autoImplicit false

namespace Section5PowerCode

variable {F ι J : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

theorem tilted_monomial_match {k D : ℕ} (hD : D+2 ≤ k)
    (χ : AddChar F ℝ) (hχ : χ ≠ 0) (v : ι → F) (hv : Function.Injective v)
    (w : ι → ℝ) (d : ι →₀ ℕ) (hd : d.sum (fun _ e => e) ≤ D) :
    (∑ t : Fin k → F, frameWeight χ v w t*(∏ i, codeSign χ v t i ^ d i))=
      ∑ x : ι → Bool, Section5BooleanFrame.weight w x*
        (∏ i, Section5BooleanFrame.sign x i ^ d i) := by
  have hp : (MvPolynomial.monomial d 1 : MvPolynomial ι ℝ).totalDegree+2 ≤ k := by
    have he := MvPolynomial.totalDegree_monomial_le d (1 : ℝ)
    change (MvPolynomial.monomial d 1 : MvPolynomial ι ℝ).totalDegree ≤
      d.sum (fun _ e => e) at he
    omega
  have he := codeSign_tilted_polynomial_mean χ hχ v hv w (MvPolynomial.monomial d 1) hp
  simp only [MvPolynomial.eval_monomial,one_mul,Finsupp.prod_pow] at he
  simpa only [Section5SignMoments.mean,frameWeight,Section5BooleanFrame.weight,
    Section5BooleanFrame.amplitude,Finset.mul_sum,mul_assoc] using he



end Section5PowerCode

end
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι J : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
theorem solution {k D : ℕ} (hD : D+2 ≤ k)
    (χ : AddChar F ℝ) (hχ : χ ≠ 0) (v : ι → F) (hv : Function.Injective v)
    (w : ι → ℝ) (P : MvPolynomial (J × ι) ℝ) (hP : P.totalDegree ≤ D) :
    (∑ t : J → Fin k → F, (∏ r, Section5PowerCode.frameWeight χ v w (t r))*
      MvPolynomial.eval (fun z => Section5PowerCode.codeSign χ v (t z.1) z.2) P)=
      ∑ x : J → ι → Bool, (∏ r, Section5BooleanFrame.weight w (x r))*
        MvPolynomial.eval (fun z => Section5BooleanFrame.sign (x z.1) z.2) P := by
  exact Section5SignMoments.tensor_polynomial_mean_match _ _ _ _ D
    (Section5PowerCode.tilted_monomial_match hD χ hχ v hv w) P hP
