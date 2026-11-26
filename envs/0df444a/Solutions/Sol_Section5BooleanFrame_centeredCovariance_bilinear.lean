-- Prove2me | solution 1 for Section5BooleanFrame.centeredCovariance_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:51:59.186724+00:00
-- url     : https://prove2.me/submissions/57f6b1fc-f6de-4800-a005-0b71af2d1c71

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CovarianceTracePolynomial
import Definitions.Def_Section5Verified_Section5SampleCovarianceBilinear
import Definitions.Def_Section5Verified_Section5TiltedFrameTail
import Mathlib
section
set_option autoImplicit false

namespace Section5BooleanFrame

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]







theorem triple_sum_rotate {κ : Type*} [Fintype κ] (f : ι → ι → κ → ℝ) :
    (∑ i, ∑ j, ∑ x, f i j x)=∑ x, ∑ i, ∑ j, f i j x := by
  calc
    _ = ∑ i, ∑ x, ∑ j, f i j x := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem populationCovariance_bilinear (w u v : ι → ℝ) :
    bilinear (populationCovariance w) u v=tiltedMean w (fun x => amplitude u x*amplitude v x) := by
  have hexp (x : ι → Bool) : amplitude u x*amplitude v x=
      ∑ i, ∑ j, (u i*sign x i)*(v j*sign x j) := by
    exact Finset.sum_mul_sum _ _ _ _
  simp only [bilinear,populationCovariance,tiltedMean,hexp,Finset.mul_sum,Finset.sum_mul]
  rw [triple_sum_rotate]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring



end Section5BooleanFrame

end
set_option autoImplicit false
namespace Section5BooleanFrame
end Section5BooleanFrame
open Section5BooleanFrame
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
theorem solution (hJ : Fintype.card J ≠ 0)
    (w u v : ι → ℝ) (x : J → ι → Bool) :
    Section5BooleanFrame.bilinear (Section5SignMoments.centeredCovariance (Section5BooleanFrame.populationCovariance w)
      (fun r => Section5BooleanFrame.sign (x r))) u v=
      (Fintype.card J : ℝ)⁻¹*(∑ r, (Section5BooleanFrame.amplitude u (x r)*Section5BooleanFrame.amplitude v (x r)-
        Section5BooleanFrame.tiltedMean w (fun y => Section5BooleanFrame.amplitude u y*Section5BooleanFrame.amplitude v y))) := by
  have he (i j : ι) :
      u i*((Fintype.card J : ℝ)⁻¹*(∑ r : J, Section5BooleanFrame.sign (x r) i*Section5BooleanFrame.sign (x r) j)-
        Section5BooleanFrame.populationCovariance w i j)*v j=
      (Fintype.card J : ℝ)⁻¹*(∑ r : J, (u i*Section5BooleanFrame.sign (x r) i)*(v j*Section5BooleanFrame.sign (x r) j))-
        u i*Section5BooleanFrame.populationCovariance w i j*v j := by
    simp only [Finset.mul_sum,Finset.sum_mul,mul_sub,sub_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [Section5BooleanFrame.bilinear,Section5SignMoments.centeredCovariance,he,Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [Section5BooleanFrame.triple_sum_rotate]
  have hprod (r : J) : (∑ i, ∑ j, (u i*Section5BooleanFrame.sign (x r) i)*(v j*Section5BooleanFrame.sign (x r) j))=
      Section5BooleanFrame.amplitude u (x r)*Section5BooleanFrame.amplitude v (x r) := by
    exact (Finset.sum_mul_sum _ _ _ _).symm
  simp only [hprod]
  rw [show (∑ i, ∑ j, u i*Section5BooleanFrame.populationCovariance w i j*v j)=
    Section5BooleanFrame.tiltedMean w (fun y => Section5BooleanFrame.amplitude u y*Section5BooleanFrame.amplitude v y) from Section5BooleanFrame.populationCovariance_bilinear w u v]
  rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,mul_sub,← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hJ),one_mul]
