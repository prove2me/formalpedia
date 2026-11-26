-- Prove2me | solution 1 for Section5PowerCode.covariance_trace_moment_match
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:33.025795+00:00
-- url     : https://prove2.me/submissions/605e08d9-2fe9-4898-9279-87cfcce89522

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5CovarianceTracePolynomial
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Mathlib
import Theorems.Thm_Section5PowerCode_tilted_batch_polynomial_match
import Theorems.Thm_Section5SignMoments_covarianceTracePolynomial_degree
section
set_option autoImplicit false

namespace Section5SignMoments

variable {ι J σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]









theorem covariancePolynomial_eval (S : Matrix ι ι ℝ) (a : J → ι → ℝ) :
    (MvPolynomial.eval (fun z : J × ι => a z.1 z.2)).mapMatrix
      (covariancePolynomial S)=centeredCovariance S a := by
  ext i j
  simp [covariancePolynomial,centeredCovariance,RingHom.mapMatrix_apply]





theorem covarianceTracePolynomial_eval (S : Matrix ι ι ℝ) (p : ℕ) (a : J → ι → ℝ) :
    MvPolynomial.eval (fun z : J × ι => a z.1 z.2) (covarianceTracePolynomial S p)=
      Matrix.trace ((centeredCovariance S a)^(2*p)) := by
  unfold covarianceTracePolynomial
  rw [AddMonoidHom.map_trace]
  change Matrix.trace ((MvPolynomial.eval (fun z : J × ι => a z.1 z.2)).mapMatrix
    ((covariancePolynomial S)^(2*p)))=_
  rw [map_pow,covariancePolynomial_eval]

end Section5SignMoments

end
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι J : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
theorem solution {k : ℕ} (p : ℕ) (hp : 4*p+2 ≤ k)
    (χ : AddChar F ℝ) (hχ : χ ≠ 0) (v : ι → F) (hv : Function.Injective v)
    (w : ι → ℝ) (S : Matrix ι ι ℝ) :
    (∑ t : J → Fin k → F, (∏ r, Section5PowerCode.frameWeight χ v w (t r))*
      Matrix.trace ((Section5SignMoments.centeredCovariance S
        (fun r => Section5PowerCode.codeSign χ v (t r)))^(2*p)))=
      ∑ x : J → ι → Bool, (∏ r, Section5BooleanFrame.weight w (x r))*
        Matrix.trace ((Section5SignMoments.centeredCovariance S
          (fun r => Section5BooleanFrame.sign (x r)))^(2*p)) := by
  have he := Section5PowerCode.tilted_batch_polynomial_match hp χ hχ v hv w
    (Section5SignMoments.covarianceTracePolynomial (J := J) S p)
    (Section5SignMoments.covarianceTracePolynomial_degree S p)
  have hcode (t : J → Fin k → F) := Section5SignMoments.covarianceTracePolynomial_eval
    S p (fun r => Section5PowerCode.codeSign χ v (t r))
  have hfull (x : J → ι → Bool) := Section5SignMoments.covarianceTracePolynomial_eval
    S p (fun r => Section5BooleanFrame.sign (x r))
  simpa only [hcode,hfull] using he
