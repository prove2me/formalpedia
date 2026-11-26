-- Prove2me | solution 1 for Section5PowerCode.matrixSample_unbiased
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:20.3728+00:00
-- url     : https://prove2.me/submissions/fe939b2f-2a4c-4755-9947-3b25b06326bb

import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5CodedFrameEstimator
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Mathlib
import Theorems.Thm_Section5PowerCode_frameWeight_sum
import Theorems.Thm_Section5PowerCode_frame_diagonal_corrected_covariance
section
set_option autoImplicit false

/-! An unbiased, symmetric matrix sample. Its entries use only the measured
frame seed and an independent computational-basis outcome. They do not use the
unknown target amplitudes. No concentration or circuit bound is asserted. -/

namespace Section5PowerCode

variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]











theorem matrixSample_basis_mean {k : ℕ} (χ : AddChar F ℝ) (v : ι → F)
    (w : ι → ℝ) (hw : ∑ i, w i^2=1) (t : Fin k → F) (i j : ι) :
    (∑ y, w y^2*matrixSample χ v t y i j)=
      (codeSign χ v t i*codeSign χ v t j-(if i=j then 1 else 0))/2+
        (if i=j then w i^2 else 0) := by
  simp only [matrixSample,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hw,one_mul]
  congr 1
  by_cases h : i=j <;> simp [h]



end Section5PowerCode

end
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]
theorem solution {k : ℕ} (hk : 4 ≤ k) (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v) (w : ι → ℝ) (hw : ∑ i, w i^2=1)
    (i j : ι) :
    (∑ z : (Fin k → F) × ι, Section5PowerCode.jointWeight χ v w z*Section5PowerCode.matrixSample χ v z.1 z.2 i j)=w i*w j := by
  simp only [Section5PowerCode.jointWeight,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum]
  simp only [Section5PowerCode.matrixSample_basis_mean χ v w hw,mul_add,Finset.sum_add_distrib]
  simp only [← mul_div_assoc,mul_sub]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul]
  rw [Section5PowerCode.frameWeight_sum (by omega) χ hχ v hv w,hw]
  simp only [one_mul]
  exact Section5PowerCode.frame_diagonal_corrected_covariance hk χ hχ v hv w hw i j
